// bst_visualizer_final.cpp
// BST Visualizer - Insert/Delete/Search with validations and animations.
// Messages now show the user-entered value (not node value).
// Compile with: g++ bst_visualizer_final.cpp -o bst_vis -std=c++17 `pkg-config --cflags --libs raylib`

#include "raylib.h"
#include <iostream>
#include <string>
#include <vector>
#include <cmath>
#include <queue>
#include <algorithm>
#include <functional>
#include <cassert>

// ---------- Node ----------
struct Node {
    int value;
    Node* left;
    Node* right;
    float x, y;        // target layout position
    float animX, animY;// animated position
    float radius;
    Color color;
    Node(int v = 0, float _x = 0, float _y = 0) {
        value = v;
        left = right = nullptr;
        x = animX = _x;
        y = animY = _y;
        radius = 25.0f;
        color = SKYBLUE;
    }
};

// ---------- Globals ----------
static Node* root = nullptr;
static const int SCREEN_W = 1400;
static const int SCREEN_H = 900;

// ---------- Layout & animation helpers ----------
void ComputePositions(Node* node, float cx, float cy, float offset) {
    if (!node) return;
    node->x = cx;
    node->y = cy;
    if (node->left) ComputePositions(node->left, cx - offset, cy + 90.0f, offset * 0.6f);
    if (node->right) ComputePositions(node->right, cx + offset, cy + 90.0f, offset * 0.6f);
}

void RecomputeLayoutAndSnap(Node* r) {
    ComputePositions(r, SCREEN_W / 2.0f, 80.0f, 220.0f);
    // Initialize anim positions if zero
    std::function<void(Node*)> init = [&](Node* n) {
        if (!n) return;
        if (n->animX == 0 && n->animY == 0) {
            n->animX = n->x; n->animY = n->y;
        }
        init(n->left); init(n->right);
        };
    init(r);
}

void SmoothMoveAll(Node* node, float easing = 0.18f) {
    if (!node) return;
    node->animX += (node->x - node->animX) * easing;
    node->animY += (node->y - node->animY) * easing;
    SmoothMoveAll(node->left, easing);
    SmoothMoveAll(node->right, easing);
}

// ---------- Drawing ----------
void DrawTree(Node* node, Node* highlight = nullptr, Node* special = nullptr) {
    if (!node) return;
    if (node->left) DrawLineV({ node->animX, node->animY }, { node->left->animX, node->left->animY }, BLACK);
    if (node->right) DrawLineV({ node->animX, node->animY }, { node->right->animX, node->right->animY }, BLACK);

    // Outer highlight ring (single)
    if (node == highlight) {
        DrawCircle((int)node->animX, (int)node->animY, node->radius + 6, YELLOW);
    }
    if (node == special) {
        DrawCircle((int)node->animX, (int)node->animY, node->radius + 6, ORANGE);
    }

    DrawCircle((int)node->animX, (int)node->animY, node->radius, node->color);
    DrawCircleLines((int)node->animX, (int)node->animY, node->radius, DARKBLUE);
    DrawText(std::to_string(node->value).c_str(), (int)(node->animX - 10), (int)(node->animY - 10), 20, BLACK);

    DrawTree(node->left, highlight, special);
    DrawTree(node->right, highlight, special);
}

// ---------- Basic BST helpers ----------
std::pair<Node*, Node*> FindWithParent(Node* rootRef, int value) {
    Node* parent = nullptr;
    Node* cur = rootRef;
    while (cur) {
        if (value == cur->value) return { parent, cur };
        parent = cur;
        if (value < cur->value) cur = cur->left;
        else cur = cur->right;
    }
    return { nullptr, nullptr };
}

std::pair<Node*, Node*> FindInorderSuccessor(Node* node) {
    if (!node || !node->right) return { nullptr, nullptr };
    Node* parent = node;
    Node* cur = node->right;
    while (cur->left) {
        parent = cur;
        cur = cur->left;
    }
    return { parent, cur };
}

void ReplaceChild(Node*& rootRef, Node* parent, Node* oldChild, Node* newChild) {
    if (!parent) {
        rootRef = newChild;
    }
    else {
        if (parent->left == oldChild) parent->left = newChild;
        else if (parent->right == oldChild) parent->right = newChild;
    }
}

void DeleteNodePointer(Node*& ptr) {
    if (!ptr) return;
    delete ptr;
    ptr = nullptr;
}

// ---------- Insert immediate helper (fallback) ----------
void InsertValueImmediate(Node*& rootRef, int value) {
    if (!rootRef) {
        rootRef = new Node(value, SCREEN_W / 2.0f, 80.0f);
        rootRef->color = RED;
        RecomputeLayoutAndSnap(rootRef);
        return;
    }
    Node* cur = rootRef;
    Node* parent = nullptr;
    float offset = 220.0f;
    float x = rootRef->x, y = rootRef->y;
    while (cur) {
        parent = cur;
        if (value < cur->value) {
            x = cur->x - offset; y = cur->y + 90.0f;
            cur = cur->left;
        }
        else {
            x = cur->x + offset; y = cur->y + 90.0f;
            cur = cur->right;
        }
        offset *= 0.6f;
    }
    Node* n = new Node(value, x, y);
    n->color = RED;
    if (value < parent->value) parent->left = n; else parent->right = n;
    RecomputeLayoutAndSnap(rootRef);
}

// ---------- State machines: Insert, Delete, Search ----------

// Insert state
enum InsertStage { INS_IDLE, INS_TRAVERSING, INS_ATTACHING, INS_FINALIZE };
static InsertStage insStage = INS_IDLE;
static std::vector<Node*> insTraversalPath;
static int insTraversalIndex = 0;
static int insFramesCounter = 0;
static const int INS_STEP_FRAMES = 12;
static Node* insParent = nullptr;
static Node* insNewNode = nullptr;
static float insNewX = 0, insNewY = 0;
static bool insNewIsLeft = false;
static int insFinalizeTimer = 0; // frames to show blue after insertion
static int insValuePending = 0;

// Delete state
enum DelStage {
    DEL_IDLE, DEL_TRAVERSING, DEL_HIGHLIGHT_TARGET, DEL_HIGHLIGHT_SUCCESSOR,
    DEL_MOVE_SUCCESSOR, DEL_MOVE_CHILD_UP, DEL_SHRINK_REMOVE, DEL_FINALIZE
};
static DelStage delStage = DEL_IDLE;
static std::vector<Node*> delTraversalPath;
static int delTraversalIndex = 0;
static int delFramesCounter = 0;
static const int DEL_STEP_FRAMES = 12;
static Node* delTargetParent = nullptr;
static Node* delTargetNode = nullptr;
static Node* successorParent = nullptr;
static Node* successorNode = nullptr;
static Node* animNode = nullptr;
static Node* animReplaceNode = nullptr;
static float moveStartX = 0, moveStartY = 0, moveTargetX = 0, moveTargetY = 0;
static float animDuration = 24.0f;
static float animProgress = 0.0f;
static int delValuePending = 0; // <-- pending delete value entered by user

// Search state
enum SearchStage { S_IDLE, S_TRAVERSING, S_FLASH_FOUND, S_FLASH_NOTFOUND };
static SearchStage searchStage = S_IDLE;
static std::vector<Node*> searchPath;
static int searchIndex = 0;
static int searchFrames = 0;
static const int SEARCH_STEP_FRAMES = 12;
static int flashCount = 0;
static const int FLASH_FRAMES = 12; // frames per flash on/off
static Node* searchFinalNode = nullptr;
static int searchValuePending = 0; // <-- pending search value entered by user

// --- Status message (validations) ---
static std::string statusMessage = "";
static int statusTimer = 0; // frames: show message for 120 frames (2 sec)

// ---------- Start insertion traversal (non-blocking) ----------
void StartInsertion(int value) {
    insTraversalPath.clear();
    insTraversalIndex = 0;
    insFramesCounter = 0;
    insStage = INS_TRAVERSING;
    insParent = nullptr;
    insNewNode = nullptr;
    insNewIsLeft = false;
    insValuePending = value;

    Node* cur = root;
    Node* parent = nullptr;
    float x = SCREEN_W / 2.0f;
    float y = 80.0f;
    float offset = 220.0f;

    // if root null -> will create root directly
    if (!cur) {
        insParent = nullptr;
        insNewX = x;
        insNewY = y;
        insNewIsLeft = false;
        return;
    }

    while (cur) {
        insTraversalPath.push_back(cur);
        parent = cur;
        if (value < cur->value) {
            x = cur->x - offset; y = cur->y + 90.0f;
            cur = cur->left;
            insNewIsLeft = true;
        }
        else {
            x = cur->x + offset; y = cur->y + 90.0f;
            cur = cur->right;
            insNewIsLeft = false;
        }
        offset *= 0.6f;
    }

    insParent = parent;
    insNewX = x; insNewY = y;
}

// Attach new node (called when traversal finished)
void AttachNewNodeFromPending() {
    Node* n = new Node(insValuePending, insNewX, insNewY);
    n->color = RED;
    if (!insParent) {
        root = n;
    }
    else {
        if (insNewIsLeft) insParent->left = n;
        else insParent->right = n;
    }
    insNewNode = n;
    RecomputeLayoutAndSnap(root);
    // Start finalize timer (2 seconds)
    insFinalizeTimer = 120;
    // Set status message based on user-entered value
    statusMessage = "Inserted " + std::to_string(insValuePending);
    statusTimer = 120;
}

// ---------- Start deletion traversal (non-blocking) ----------
void StartDeletion(int value) {
    delTraversalPath.clear();
    delTraversalIndex = 0;
    delFramesCounter = 0;
    delStage = DEL_TRAVERSING;
    delTargetParent = nullptr;
    delTargetNode = nullptr;
    successorParent = nullptr;
    successorNode = nullptr;
    animNode = nullptr;
    animReplaceNode = nullptr;
    animProgress = 0;

    delValuePending = value;

    Node* cur = root;
    Node* parent = nullptr;
    while (cur) {
        delTraversalPath.push_back(cur);
        if (value == cur->value) {
            delTargetParent = parent;
            delTargetNode = cur;
            break;
        }
        parent = cur;
        if (value < cur->value) cur = cur->left;
        else cur = cur->right;
    }
    RecomputeLayoutAndSnap(root);
}

// ---------- Start search traversal ----------
void StartSearch(int value) {
    searchPath.clear();
    searchIndex = 0;
    searchFrames = 0;
    flashCount = 0;
    searchFinalNode = nullptr;
    searchStage = S_TRAVERSING;
    searchValuePending = value;

    Node* cur = root;
    while (cur) {
        searchPath.push_back(cur);
        if (value == cur->value) {
            searchFinalNode = cur;
            break;
        }
        if (value < cur->value) cur = cur->left;
        else cur = cur->right;
    }
    // if not found, searchFinalNode remains nullptr
}

// Utility: recursively finalize RED->SKYBLUE after insertion if timer elapsed
void FinalizeNewNodes(Node* n) {
    if (!n) return;
    if (n->color.r == RED.r && n->color.g == RED.g && n->color.b == RED.b) {
        n->color = SKYBLUE;
        return;
    }
    FinalizeNewNodes(n->left);
    FinalizeNewNodes(n->right);
}

// ---------- Main ----------
int main() {
    InitWindow(SCREEN_W, SCREEN_H, "BST Visualizer - Final (values displayed as entered by user)");
    SetTargetFPS(60);

    // UI
    Rectangle inputBox = { 360, 70, 160, 36 };
    Rectangle insertBtn = { 20, 70, 160, 40 };
    Rectangle deleteBtn = { 200, 70, 140, 40 };
    Rectangle searchBtn = { 360 + 180, 70, 140, 40 }; // placed to the right
    std::string inputText = "";
    bool inputFocused = false;
    enum Mode { MODE_INSERT, MODE_DELETE, MODE_SEARCH } mode = MODE_INSERT;

    // camera
    Camera2D camera = { 0 };
    camera.target = { 0,0 };
    camera.offset = { 0,0 };
    camera.zoom = 1.0f;

    // helper timers
    int insertFinalize = 0;

    while (!WindowShouldClose()) {
        Vector2 mouse = GetMousePosition();

        // UI input focus click
        if (CheckCollisionPointRec(mouse, inputBox) && IsMouseButtonPressed(MOUSE_LEFT_BUTTON)) {
            inputFocused = true;
        }
        if (!CheckCollisionPointRec(mouse, inputBox) && IsMouseButtonPressed(MOUSE_LEFT_BUTTON)) {
            inputFocused = false;
        }

        // Buttons clicked detection
        bool insertClicked = false, deleteClicked = false, searchClicked = false;
        if (IsMouseButtonPressed(MOUSE_LEFT_BUTTON)) {
            if (CheckCollisionPointRec(mouse, insertBtn)) insertClicked = true;
            if (CheckCollisionPointRec(mouse, deleteBtn)) deleteClicked = true;
            if (CheckCollisionPointRec(mouse, searchBtn)) searchClicked = true;
        }
        if (insertClicked) { inputFocused = true; mode = MODE_INSERT; }
        if (deleteClicked) { inputFocused = true; mode = MODE_DELETE; }
        if (searchClicked) { inputFocused = true; mode = MODE_SEARCH; }

        // typing into input
        if (inputFocused) {
            int key = GetCharPressed();
            while (key > 0) {
                if ((key >= '0' && key <= '9') && inputText.size() < 7) inputText.push_back((char)key);
                key = GetCharPressed();
            }
            if (IsKeyPressed(KEY_BACKSPACE) && !inputText.empty()) inputText.pop_back();
            if (IsKeyPressed(KEY_ENTER) && !inputText.empty()) {
                int v = std::stoi(inputText);
                // Decide action based on mode, obey blocking rules:
                bool animationsRunning = (delStage != DEL_IDLE) || (insStage != INS_IDLE && insStage != INS_FINALIZE) || (searchStage != S_IDLE);
                if (mode == MODE_INSERT) {
                    // Block insert if a delete is running (stability)
                    if (delStage == DEL_IDLE && insStage == INS_IDLE) {
                        StartInsertion(v);
                        inputText.clear();
                    }
                    else {
                        statusMessage = "Insert blocked until current animation finishes.";
                        statusTimer = 120;
                    }
                }
                else if (mode == MODE_DELETE) {
                    if (delStage == DEL_IDLE && searchStage == S_IDLE && insStage == INS_IDLE) {
                        StartDeletion(v);
                        inputText.clear();
                    }
                    else {
                        statusMessage = "Delete blocked until current animation finishes.";
                        statusTimer = 120;
                    }
                }
                else { // MODE_SEARCH
                    if (delStage == DEL_IDLE && insStage == INS_IDLE && searchStage == S_IDLE) {
                        StartSearch(v);
                        inputText.clear();
                    }
                    else {
                        statusMessage = "Search blocked until current animation finishes.";
                        statusTimer = 120;
                    }
                }
            }
        }

        // camera controls
        if (IsKeyDown(KEY_RIGHT)) camera.target.x += 8;
        if (IsKeyDown(KEY_LEFT))  camera.target.x -= 8;
        if (IsKeyDown(KEY_UP))    camera.target.y -= 8;
        if (IsKeyDown(KEY_DOWN))  camera.target.y += 8;
        camera.zoom += GetMouseWheelMove() * 0.05f;
        if (camera.zoom < 0.2f) camera.zoom = 0.2f;
        if (camera.zoom > 3.0f) camera.zoom = 3.0f;

        // ---------- Insert state machine ----------
        if (insStage == INS_TRAVERSING) {
            insFramesCounter++;
            if (insFramesCounter >= INS_STEP_FRAMES) {
                insFramesCounter = 0;
                if (insTraversalIndex < (int)insTraversalPath.size()) {
                    insTraversalIndex++;
                }
                else {
                    // attach node now
                    insStage = INS_ATTACHING;
                    AttachNewNodeFromPending();
                    // after attaching, go to finalize stage where the new node will become blue for 120 frames
                    insStage = INS_FINALIZE;
                }
            }
        }
        else if (insStage == INS_FINALIZE) {
            if (insFinalizeTimer > 0) {
                insFinalizeTimer--;
                if (insFinalizeTimer == 0) {
                    FinalizeNewNodes(root);
                    insNewNode = nullptr;
                    insStage = INS_IDLE;
                }
            }
        }

        // ---------- Delete state machine ----------
        if (delStage == DEL_TRAVERSING) {
            delFramesCounter++;
            if (delFramesCounter >= DEL_STEP_FRAMES) {
                delFramesCounter = 0;
                if (delTraversalIndex < (int)delTraversalPath.size()) {
                    delTraversalIndex++;
                }
                else {
                    if (!delTargetNode) {
                        // Not found -> show message using user-entered value
                        statusMessage = "Value " + std::to_string(delValuePending) + " not found for deletion";
                        statusTimer = 120;
                        delStage = DEL_IDLE;
                        delTraversalPath.clear();
                        delTraversalIndex = 0;
                    }
                    else {
                        delStage = DEL_HIGHLIGHT_TARGET;
                        delFramesCounter = 0;
                    }
                }
            }
        }
        else if (delStage == DEL_HIGHLIGHT_TARGET) {
            delFramesCounter++;
            if (delFramesCounter >= 30) {
                // decide deletion case
                if (!delTargetNode->left && !delTargetNode->right) {
                    // leaf
                    delStage = DEL_SHRINK_REMOVE;
                    animNode = delTargetNode;
                    animProgress = 0;
                }
                else if (delTargetNode->left && delTargetNode->right) {
                    auto pr = FindInorderSuccessor(delTargetNode);
                    successorParent = pr.first ? pr.first : delTargetNode;
                    successorNode = pr.second;
                    if (successorNode) delStage = DEL_HIGHLIGHT_SUCCESSOR;
                    else delStage = DEL_FINALIZE;
                    delFramesCounter = 0;
                }
                else {
                    // one-child
                    delStage = DEL_MOVE_CHILD_UP;
                    if (delTargetNode->left) animNode = delTargetNode->left;
                    else animNode = delTargetNode->right;
                    moveStartX = animNode->animX; moveStartY = animNode->animY;
                    moveTargetX = delTargetNode->x; moveTargetY = delTargetNode->y;
                    animProgress = 0;
                }
            }
        }
        else if (delStage == DEL_HIGHLIGHT_SUCCESSOR) {
            delFramesCounter++;
            if (delFramesCounter >= 30) {
                // start moving successor
                delStage = DEL_MOVE_SUCCESSOR;
                animNode = successorNode;
                animReplaceNode = delTargetNode;
                moveStartX = successorNode->animX; moveStartY = successorNode->animY;
                moveTargetX = delTargetNode->x; moveTargetY = delTargetNode->y;
                animProgress = 0;
            }
        }
        else if (delStage == DEL_MOVE_SUCCESSOR) {
            animProgress += 1.0f / animDuration;
            if (animProgress > 1.0f) animProgress = 1.0f;
            animNode->animX = moveStartX + (moveTargetX - moveStartX) * animProgress;
            animNode->animY = moveStartY + (moveTargetY - moveStartY) * animProgress;
            if (animProgress >= 1.0f) {
                // copy value and remove successor structurally
                delTargetNode->value = successorNode->value;
                // unlink successor
                if (successorParent->left == successorNode) successorParent->left = successorNode->right;
                else if (successorParent->right == successorNode) successorParent->right = successorNode->right;
                DeleteNodePointer(successorNode);
                successorNode = nullptr;
                successorParent = nullptr;
                animNode = nullptr; animReplaceNode = nullptr;
                RecomputeLayoutAndSnap(root);
                delStage = DEL_FINALIZE;
                delFramesCounter = 0;
                // show success message using user-entered value
                statusMessage = "Deleted " + std::to_string(delValuePending);
                statusTimer = 120;
            }
        }
        else if (delStage == DEL_MOVE_CHILD_UP) {
            animProgress += 1.0f / animDuration;
            if (animProgress > 1.0f) animProgress = 1.0f;
            animNode->animX = moveStartX + (moveTargetX - moveStartX) * animProgress;
            animNode->animY = moveStartY + (moveTargetY - moveStartY) * animProgress;
            if (animProgress >= 1.0f) {
                Node* parent = delTargetParent;
                if (!parent) {
                    // root
                    if (delTargetNode->left) root = delTargetNode->left;
                    else root = delTargetNode->right;
                }
                else {
                    if (parent->left == delTargetNode) {
                        if (delTargetNode->left) parent->left = delTargetNode->left;
                        else parent->left = delTargetNode->right;
                    }
                    else if (parent->right == delTargetNode) {
                        if (delTargetNode->left) parent->right = delTargetNode->left;
                        else parent->right = delTargetNode->right;
                    }
                }
                DeleteNodePointer(delTargetNode);
                delTargetNode = nullptr;
                animNode = nullptr;
                RecomputeLayoutAndSnap(root);
                delStage = DEL_FINALIZE;
                // success message using user-entered value
                statusMessage = "Deleted " + std::to_string(delValuePending);
                statusTimer = 120;
            }
        }
        else if (delStage == DEL_SHRINK_REMOVE) {
            if (!animNode) delStage = DEL_FINALIZE;
            else {
                animProgress += 1.0f / (animDuration / 1.5f);
                animNode->radius = 25.0f * (1.0f - animProgress);
                animNode->color = Fade(RED, 1.0f - animProgress);
                if (animProgress >= 1.0f) {
                    Node* parent = delTargetParent;
                    // show deleted value using pending
                    if (!parent) {
                        DeleteNodePointer(root);
                    }
                    else {
                        if (parent->left == animNode) parent->left = nullptr;
                        else if (parent->right == animNode) parent->right = nullptr;
                        DeleteNodePointer(animNode);
                    }
                    animNode = nullptr;
                    delTargetNode = nullptr;
                    RecomputeLayoutAndSnap(root);
                    delStage = DEL_FINALIZE;
                    statusMessage = "Deleted " + std::to_string(delValuePending);
                    statusTimer = 120;
                }
            }
        }
        else if (delStage == DEL_FINALIZE) {
            delFramesCounter++;
            if (delFramesCounter > 20) {
                delStage = DEL_IDLE;
                delTraversalPath.clear();
                delTraversalIndex = 0;
                delFramesCounter = 0;
            }
        }

        // ---------- Search state machine ----------
        if (searchStage == S_TRAVERSING) {
            // Block if deletion or insertion currently animating (Option 2)
            if (delStage != DEL_IDLE || insStage != INS_IDLE) {
                // wait
            }
            else {
                searchFrames++;
                if (searchFrames >= SEARCH_STEP_FRAMES) {
                    searchFrames = 0;
                    if (searchIndex < (int)searchPath.size()) {
                        searchIndex++;
                    }
                    else {
                        if (searchPath.empty()) {
                            searchStage = S_FLASH_NOTFOUND;
                            searchFinalNode = nullptr;
                            statusMessage = "Not found " + std::to_string(searchValuePending);
                            statusTimer = 120;
                        }
                        else {
                            if (searchFinalNode != nullptr) {
                                searchStage = S_FLASH_FOUND;
                                statusMessage = "Found " + std::to_string(searchValuePending);
                                statusTimer = 120;
                            }
                            else {
                                searchStage = S_FLASH_NOTFOUND;
                                searchFinalNode = searchPath.back();
                                statusMessage = "Not found " + std::to_string(searchValuePending);
                                statusTimer = 120;
                            }
                        }
                    }
                }
            }
        }
        else if (searchStage == S_FLASH_FOUND) {
            searchFrames++;
            if (searchFrames >= FLASH_FRAMES) {
                searchFrames = 0;
                flashCount++;
                if (flashCount >= 6) { // 3 flashes (on/off)
                    searchStage = S_IDLE;
                    searchPath.clear();
                    searchIndex = 0;
                    flashCount = 0;
                    searchFinalNode = nullptr;
                }
            }
        }
        else if (searchStage == S_FLASH_NOTFOUND) {
            searchFrames++;
            if (searchFrames >= FLASH_FRAMES) {
                searchFrames = 0;
                flashCount++;
                if (flashCount >= 6) {
                    searchStage = S_IDLE;
                    searchPath.clear();
                    searchIndex = 0;
                    flashCount = 0;
                    searchFinalNode = nullptr;
                }
            }
        }

        // finalize inserted nodes color when timer runs out (ensures node stays blue for 2 seconds)
        if (insFinalizeTimer > 0) {
            insFinalizeTimer--;
            if (insFinalizeTimer == 0) {
                FinalizeNewNodes(root);
                insNewNode = nullptr;
                insStage = INS_IDLE;
            }
        }

        // decrement status message timer
        if (statusTimer > 0) {
            statusTimer--;
            if (statusTimer == 0) statusMessage.clear();
        }

        // Smooth move
        SmoothMoveAll(root);

        // ---------- Drawing ----------
        BeginDrawing();
        ClearBackground(RAYWHITE);

        BeginMode2D(camera);

        // Determine del highlight node
        Node* delHighlight = nullptr;
        if (delStage == DEL_TRAVERSING) {
            if (delTraversalIndex < (int)delTraversalPath.size()) delHighlight = delTraversalPath[delTraversalIndex];
            else if (!delTraversalPath.empty()) delHighlight = delTraversalPath.back();
        }
        else if (delStage == DEL_HIGHLIGHT_TARGET && delTargetNode) delHighlight = delTargetNode;
        else if (delStage == DEL_HIGHLIGHT_SUCCESSOR && successorNode) delHighlight = successorNode;

        // Determine insert highlight: current visited node for insertion
        Node* insHighlight = nullptr;
        if (insStage == INS_TRAVERSING) {
            if (insTraversalIndex < (int)insTraversalPath.size()) insHighlight = insTraversalPath[insTraversalIndex];
            else if (!insTraversalPath.empty()) insHighlight = insTraversalPath.back();
        }

        // Determine search current node and list of visited for rings
        Node* searchCurrent = nullptr;
        if (!searchPath.empty() && searchIndex > 0) {
            int idx = std::min(searchIndex - 1, (int)searchPath.size() - 1);
            searchCurrent = searchPath[idx];
        }

        // Composite drawing: pass delHighlight as primary highlight, then draw search rings and insert rings separately
        DrawTree(root, delHighlight, animNode);

        // Draw insertion traversal rings (visited nodes remain yellow while traversing)
        if (insStage == INS_TRAVERSING) {
            // populate traversal list if empty (edge case)
            if (insTraversalPath.empty() && root) {
                Node* tmp = root;
                while (tmp) {
                    insTraversalPath.push_back(tmp);
                    if (insValuePending < tmp->value) tmp = tmp->left;
                    else tmp = tmp->right;
                }
            }
            for (int i = 0; i < std::min(insTraversalIndex, (int)insTraversalPath.size()); ++i) {
                Node* n = insTraversalPath[i];
                DrawCircle((int)n->animX, (int)n->animY, n->radius + 6, Fade(YELLOW, 0.85f));
            }
        }

        // Draw search visited rings
        if (searchStage == S_TRAVERSING || searchStage == S_FLASH_FOUND || searchStage == S_FLASH_NOTFOUND) {
            for (int i = 0; i < std::min(searchIndex, (int)searchPath.size()); ++i) {
                Node* n = searchPath[i];
                DrawCircle((int)n->animX, (int)n->animY, n->radius + 6, Fade(YELLOW, 0.85f));
            }
        }

        // Flashing on found/notfound
        if (searchStage == S_FLASH_FOUND && searchFinalNode) {
            bool visible = ((flashCount % 2) == 0);
            if (visible) DrawCircle((int)searchFinalNode->animX, (int)searchFinalNode->animY, searchFinalNode->radius + 8, GREEN);
        }
        else if (searchStage == S_FLASH_NOTFOUND && searchFinalNode) {
            bool visible = ((flashCount % 2) == 0);
            if (visible) DrawCircle((int)searchFinalNode->animX, (int)searchFinalNode->animY, searchFinalNode->radius + 8, RED);
        }

        EndMode2D();

        // UI top
        DrawRectangle(0, 0, SCREEN_W, 160, LIGHTGRAY);
        DrawText("BST Visualizer - Insert / Delete (Option C) / Search (Option C) - Final", 20, 18, 18, BLACK);
        DrawText("Click Insert/Delete/Search then type value and press Enter. Search waits while delete/insert animations run.", 20, 40, 16, DARKGRAY);

        // Draw buttons
        auto DrawButton = [&](Rectangle r, const char* label) {
            Color c = CheckCollisionPointRec(mouse, r) ? GRAY : LIGHTGRAY;
            DrawRectangleRec(r, c);
            DrawRectangleLines((int)r.x, (int)r.y, (int)r.width, (int)r.height, BLACK);
            DrawText(label, (int)r.x + 10, (int)r.y + 8, 20, BLACK);
            };
        DrawButton(insertBtn, "Insert");
        DrawButton(deleteBtn, "Delete");
        DrawButton(searchBtn, "Search");

        // Input box
        DrawRectangleRec(inputBox, WHITE);
        DrawRectangleLines((int)inputBox.x, (int)inputBox.y, (int)inputBox.width, (int)inputBox.height, BLACK);
        DrawText(inputText.c_str(), (int)inputBox.x + 8, (int)inputBox.y + 6, 20, BLACK);
        std::string modeHint = (mode == MODE_INSERT) ? "(insert mode)" : (mode == MODE_DELETE ? "(delete mode)" : "(search mode)");
        DrawText(modeHint.c_str(), (int)inputBox.x + 8, (int)(inputBox.y + inputBox.height + 4), 14, DARKGRAY);

        // Status message area (center top)
        if (!statusMessage.empty()) {
            int width = MeasureText(statusMessage.c_str(), 20);
            DrawRectangle(SCREEN_W / 2 - width / 2 - 10, 120, width + 20, 36, Fade(LIGHTGRAY, 0.95f));
            DrawRectangleLines(SCREEN_W / 2 - width / 2 - 10, 120, width + 20, 36, BLACK);
            DrawText(statusMessage.c_str(), SCREEN_W / 2 - width / 2, 128, 20, BLACK);
        }

        // small instructions
        DrawText("Arrow keys to pan, mouse wheel to zoom.", 620, 100, 16, DARKGRAY);

        EndDrawing();

        // After draw: handle button clicks that set focus/mode
        if (IsMouseButtonPressed(MOUSE_LEFT_BUTTON)) {
            if (CheckCollisionPointRec(mouse, insertBtn)) { inputFocused = true; mode = MODE_INSERT; }
            if (CheckCollisionPointRec(mouse, deleteBtn)) { inputFocused = true; mode = MODE_DELETE; }
            if (CheckCollisionPointRec(mouse, searchBtn)) { inputFocused = true; mode = MODE_SEARCH; }
        }

        // --- Advance insTraversalPath population at start of insStage ---
        if (insStage == INS_TRAVERSING && insTraversalPath.empty()) {
            if (root) {
                Node* tmp = root;
                while (tmp) {
                    insTraversalPath.push_back(tmp);
                    if (insValuePending < tmp->value) tmp = tmp->left;
                    else tmp = tmp->right;
                }
            }
            insTraversalIndex = 0;
        }

    } // main loop

    // Cleanup tree
    std::function<void(Node*)> cleanup = [&](Node* n) {
        if (!n) return;
        cleanup(n->left);
        cleanup(n->right);
        delete n;
        };
    cleanup(root);

    CloseWindow();
    return 0;
}
