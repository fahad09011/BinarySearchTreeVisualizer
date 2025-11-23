// bst_visualizer_delete.cpp
// BST Visualizer with Insert + Delete (Option C step-by-step replace animation)
// Requires raylib

#include "raylib.h"
#include <string>
#include <vector>
#include <cmath>
#include <queue>
#include <algorithm>
#include <functional>

// ---------- Node ----------
struct Node {
    int value;
    Node* left;
    Node* right;
    float x, y;    // desired layout position
    float animX, animY; // animated position for smooth movement
    float radius;
    Color color;
    Node(int v, float _x = 0, float _y = 0) {
        value = v;
        left = right = nullptr;
        x = animX = _x;
        y = animY = _y;
        radius = 25;
        color = SKYBLUE;
    }
};

// ---------- BST utility ----------
static Node* root = nullptr;

// compute layout positions (desired x,y) recursively
void ComputePositions(Node* node, float cx, float cy, float offset) {
    if (!node) return;
    node->x = cx;
    node->y = cy;
    if (node->left) ComputePositions(node->left, cx - offset, cy + 90, offset * 0.6f);
    if (node->right) ComputePositions(node->right, cx + offset, cy + 90, offset * 0.6f);
}

// smooth animation toward desired positions
void SmoothMoveAll(Node* node, float easing = 0.2f) {
    if (!node) return;
    node->animX += (node->x - node->animX) * easing;
    node->animY += (node->y - node->animY) * easing;
    SmoothMoveAll(node->left, easing);
    SmoothMoveAll(node->right, easing);
}

// draw tree recursively, with optional highlight pointers
void DrawTree(Node* node, Node* highlight, Node* special = nullptr) {
    if (!node) return;
    if (node->left) DrawLineV({ node->animX, node->animY }, { node->left->animX, node->left->animY }, BLACK);
    if (node->right) DrawLineV({ node->animX, node->animY }, { node->right->animX, node->right->animY }, BLACK);

    Color fill = node->color;
    if (node == highlight) {
        // draw highlight outer ring
        DrawCircle((int)node->animX, (int)node->animY, node->radius + 6, YELLOW);
    }
    if (node == special) {
        DrawCircle((int)node->animX, (int)node->animY, node->radius + 6, ORANGE);
    }

    DrawCircle((int)node->animX, (int)node->animY, node->radius, fill);
    DrawCircleLines((int)node->animX, (int)node->animY, node->radius, DARKBLUE);
    DrawText(std::to_string(node->value).c_str(), (int)(node->animX - 10), (int)(node->animY - 10), 20, BLACK);

    DrawTree(node->left, highlight, special);
    DrawTree(node->right, highlight, special);
}

// find node pointer and parent for a value (returns parent, node)
std::pair<Node*, Node*> FindWithParent(Node* root, int value) {
    Node* parent = nullptr;
    Node* cur = root;
    while (cur) {
        if (value == cur->value) return { parent, cur };
        parent = cur;
        if (value < cur->value) cur = cur->left;
        else cur = cur->right;
    }
    return { nullptr, nullptr };
}

// find inorder successor and its parent (leftmost in right subtree)
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

// replace child link in parent with newChild (handles null parent => root)
void ReplaceChild(Node*& rootRef, Node* parent, Node* oldChild, Node* newChild) {
    if (!parent) {
        rootRef = newChild;
    }
    else {
        if (parent->left == oldChild) parent->left = newChild;
        else if (parent->right == oldChild) parent->right = newChild;
    }
}

// Recompute layout and reset animation anchors when structure changes
void RecomputeLayoutAndSnap(Node*& rootRef, int screenW) {
    ComputePositions(rootRef, screenW / 2.0f, 80.0f, 220.0f);
    // If a node has zero anim pos (new nodes), initialize anim pos to their x,y
    std::function<void(Node*)> init = [&](Node* n) {
        if (!n) return;
        // if anim is 0, set to desired pos (helps with newly created nodes)
        if (n->animX == 0 && n->animY == 0) {
            n->animX = n->x;
            n->animY = n->y;
        }
        init(n->left);
        init(n->right);
        };
    init(rootRef);
}

// ---------- Insert (keeps previous behavior) ----------
void InsertValue(Node*& rootRef, int value, int screenW) {
    if (!rootRef) {
        rootRef = new Node(value, screenW / 2.0f, 80.0f);
        rootRef->color = RED; // new node briefly red; animator will set to SKYBLUE later
        RecomputeLayoutAndSnap(rootRef, screenW);
        return;
    }
    Node* cur = rootRef;
    Node* parent = nullptr;
    float offset = 220.0f;
    float x = rootRef->x, y = rootRef->y;
    while (cur) {
        parent = cur;
        if (value < cur->value) {
            x = cur->x - offset; y = cur->y + 90;
            cur = cur->left;
        }
        else {
            x = cur->x + offset; y = cur->y + 90;
            cur = cur->right;
        }
        offset *= 0.6f;
    }
    Node* n = new Node(value, x, y);
    n->color = RED;
    if (value < parent->value) parent->left = n; else parent->right = n;
    RecomputeLayoutAndSnap(rootRef, screenW);
}

// ---------- Deletion state machine (Option C) ----------
enum DelStage {
    DEL_IDLE,
    DEL_TRAVERSING,       // highlight visited nodes
    DEL_HIGHLIGHT_TARGET, // highlight final node
    DEL_HIGHLIGHT_SUCCESSOR, // when 2-child: highlight successor
    DEL_MOVE_SUCCESSOR,   // animate successor moving to target position
    DEL_MOVE_CHILD_UP,    // animate child moving up for one-child
    DEL_SHRINK_REMOVE,    // leaf: shrink & remove
    DEL_REWIRING,         // perform pointer changes
    DEL_FINALIZE          // recompute layout and smooth to final
};

static DelStage delStage = DEL_IDLE;
static std::vector<Node*> delTraversalPath; // nodes visited
static int delTraversalIndex = 0;
static int delFramesCounter = 0;
static const int DEL_STEP_FRAMES = 12;
static Node* delTargetParent = nullptr;
static Node* delTargetNode = nullptr;
static bool delTargetIsLeft = false;

// For two-child case
static Node* successorParent = nullptr;
static Node* successorNode = nullptr;

// For animated moves
static float animDuration = 24.0f;
static float animProgress = 0.0f;
static float moveStartX = 0, moveStartY = 0;
static float moveTargetX = 0, moveTargetY = 0;
static Node* animNode = nullptr; // node being animated (moving)
static Node* animReplaceNode = nullptr; // target node in which value will be placed (for successor moving)

// begin deletion process: collect traversal path and find node
void StartDeletion(int value, int screenW) {
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

    // simulate traversal and collect path
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
    RecomputeLayoutAndSnap(root, screenW);
    // if not found -> DEL_IDLE after a short notice (handled externally by caller)
    if (!delTargetNode) {
        delStage = DEL_IDLE;
        delTraversalPath.clear();
    }
}

// Helper to unlink successor (used after moving)
void UnlinkSuccessor(Node*& rootRef, Node* succParent, Node* succ) {
    // succ has no left child by definition (leftmost). It may have right child.
    Node* child = succ->right;
    if (succParent == succ) {
        // parent's right was succ (means succ was immediate right child of target)
        // This case means the node to delete had right child and the successor is that right child.
        if (succParent == nullptr) {
            rootRef = child;
        }
        else {
            // special handling - handled by ReplaceChild externally
            // but we won't reach here
            ;
        }
    }
    else {
        // replace succParent->left with child
        if (succParent->left == succ) succParent->left = child;
    }
}

// Actually remove a node pointer (delete memory)
void DeleteNodePointer(Node*& ptr) {
    if (!ptr) return;
    // naive delete (we assume no external references remain)
    delete ptr;
    ptr = nullptr;
}

// find parent of a given node (pointer equality)
Node* FindParent(Node* rootRef, Node* child) {
    if (!rootRef || rootRef == child) return nullptr;
    Node* parent = nullptr;
    Node* cur = rootRef;
    while (cur && cur != child) {
        parent = cur;
        if (child->value < cur->value) cur = cur->left;
        else if (child->value > cur->value) cur = cur->right;
        else {
            // equal values might exist; but pointer-equality search:
            // search by pointers: traverse tree until finding child pointer
            // fallback: do a full pointer search
            std::function<Node* (Node*)> findParentByPtr = [&](Node* n)->Node* {
                if (!n) return nullptr;
                if (n->left == child || n->right == child) return n;
                Node* p = findParentByPtr(n->left);
                if (p) return p;
                return findParentByPtr(n->right);
                };
            return findParentByPtr(rootRef);
        }
    }
    // Not reliable for duplicates; fallback pointer-based:
    std::function<Node* (Node*)> findParentByPtr = [&](Node* n)->Node* {
        if (!n) return nullptr;
        if (n->left == child || n->right == child) return n;
        Node* p = findParentByPtr(n->left);
        if (p) return p;
        return findParentByPtr(n->right);
        };
    return findParentByPtr(rootRef);
}

// perform pointer-level deletion (no animations) helper - used at rewiring stage
void DeleteNodeStructural(Node*& rootRef, Node* parent, Node* node) {
    if (!node) return;
    // Case: leaf
    if (!node->left && !node->right) {
        ReplaceChild(rootRef, parent, node, nullptr);
        DeleteNodePointer(node);
        return;
    }
    // Case: one child
    if (!node->left && node->right) {
        ReplaceChild(rootRef, parent, node, node->right);
        // detach node pointer (avoid deleting moved child)
        // free node memory
        DeleteNodePointer(node);
        return;
    }
    if (node->left && !node->right) {
        ReplaceChild(rootRef, parent, node, node->left);
        DeleteNodePointer(node);
        return;
    }
    // Case: two children (find inorder successor)
    Node* succParent = node;
    Node* succ = node->right;
    while (succ->left) {
        succParent = succ;
        succ = succ->left;
    }
    // copy successor value into node
    node->value = succ->value;
    // then remove successor (which has at most right child)
    if (succParent->left == succ) succParent->left = succ->right;
    else succParent->right = succ->right;
    DeleteNodePointer(succ);
}

// ---------- UI & Main loop ----------
int main() {
    const int screenW = 1400;
    const int screenH = 900;
    InitWindow(screenW, screenH, "BST Visualizer - Insert & Delete (Option C step-by-step)");
    SetTargetFPS(60);

    // UI
    Rectangle inputBox = { 360, 70, 160, 36 };
    Rectangle insertBtn = { 20, 70, 160, 40 };
    Rectangle deleteBtn = { 200, 70, 140, 40 };
    std::string inputText = "";
    bool inputFocused = false;
    bool deleteMode = false; // if true next Enter or Delete button acts as delete

    // camera
    Camera2D camera = { 0 };
    camera.target = { 0,0 };
    camera.offset = { 0,0 };
    camera.zoom = 1.0f;

    // initialization: small sample nodes (optional)
    // root = new Node(50, screenW/2, 80); root->color = SKYBLUE;
    // RecomputeLayoutAndSnap(root, screenW);

    // animation helpers
    Node* insertAnimatingNode = nullptr;
    int insertFinalize = 0;

    // deletion animation state variables local to main
    delStage = DEL_IDLE;
    delTraversalPath.clear();
    delTraversalIndex = 0;
    delFramesCounter = 0;
    animNode = nullptr;
    animReplaceNode = nullptr;

    while (!WindowShouldClose()) {
        // --- UI input focus detection ---
        Vector2 mouse = GetMousePosition();
        if (CheckCollisionPointRec(mouse, inputBox) && IsMouseButtonPressed(MOUSE_LEFT_BUTTON)) {
            inputFocused = true;
        }
        if (!CheckCollisionPointRec(mouse, inputBox) && IsMouseButtonPressed(MOUSE_LEFT_BUTTON)) {
            inputFocused = false;
        }

        // insert / delete button behavior
        auto DrawButton = [&](Rectangle r, const char* label) -> bool {
            Vector2 m = GetMousePosition();
            bool hover = CheckCollisionPointRec(m, r);
            Color c = hover ? GRAY : LIGHTGRAY;
            DrawRectangleRec(r, c);
            DrawRectangleLines((int)r.x, (int)r.y, (int)r.width, (int)r.height, BLACK);
            DrawText(label, (int)r.x + 10, (int)r.y + 8, 20, BLACK);
            if (hover && IsMouseButtonPressed(MOUSE_LEFT_BUTTON)) return true;
            return false;
            };

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
                if (!deleteMode) {
                    // start insertion traversal animation: for simplicity just insert and mark red
                    InsertValue(root, v, screenW);
                    // newly inserted nodes are red; set a short timer to change to blue
                    insertAnimatingNode = nullptr; // detection - we'll find any RED node and finalize
                    insertFinalize = 60;
                    inputText.clear();
                }
                else {
                    // start deletion process
                    StartDeletion(std::stoi(inputText), screenW);
                    deleteMode = false;
                    inputText.clear();
                }
            }
        }

        // Buttons (drawn in the draw section but check clicks here)
        bool insertClicked = false;
        bool deleteClicked = false;
        // We'll detect click by polling mouse & bounds (drawn later but we need the click boolean now)
        if (IsMouseButtonPressed(MOUSE_LEFT_BUTTON)) {
            if (CheckCollisionPointRec(mouse, insertBtn)) insertClicked = true;
            if (CheckCollisionPointRec(mouse, deleteBtn)) deleteClicked = true;
        }
        if (insertClicked) {
            inputFocused = true;
            deleteMode = false;
        }
        if (deleteClicked) {
            inputFocused = true;
            deleteMode = true;
        }

        // Camera controls
        if (IsKeyDown(KEY_RIGHT)) camera.target.x += 8;
        if (IsKeyDown(KEY_LEFT))  camera.target.x -= 8;
        if (IsKeyDown(KEY_UP))    camera.target.y -= 8;
        if (IsKeyDown(KEY_DOWN))  camera.target.y += 8;
        camera.zoom += GetMouseWheelMove() * 0.05f;
        if (camera.zoom < 0.2f) camera.zoom = 0.2f;
        if (camera.zoom > 3.0f) camera.zoom = 3.0f;

        // --- Manage insert finalize color change ---
        if (insertFinalize > 0) {
            insertFinalize--;
            if (insertFinalize == 0) {
                // find any RED node and set to SKYBLUE (simple approach)
                std::function<void(Node*)> finalizeRed = [&](Node* n) {
                    if (!n) return;
                    if (n->color.r == RED.r && n->color.g == RED.g && n->color.b == RED.b) {
                        n->color = SKYBLUE;
                        return;
                    }
                    finalizeRed(n->left);
                    finalizeRed(n->right);
                    };
                finalizeRed(root);
            }
        }

        // --- Deletion state machine updates ---
        if (delStage == DEL_TRAVERSING) {
            delFramesCounter++;
            if (delFramesCounter >= DEL_STEP_FRAMES) {
                delFramesCounter = 0;
                if (delTraversalIndex < (int)delTraversalPath.size()) {
                    // highlight current visited
                    Node* vis = delTraversalPath[delTraversalIndex];
                    // briefly set color to YELLOW for visual effect, but preserve later
                    // We'll keep highlight node separately for drawing
                    delTraversalIndex++;
                }
                else {
                    // traversal completed; check if target found
                    if (!delTargetNode) {
                        // not found, go idle
                        delStage = DEL_IDLE;
                        delTraversalPath.clear();
                        delTraversalIndex = 0;
                    }
                    else {
                        // found target
                        delStage = DEL_HIGHLIGHT_TARGET;
                        delFramesCounter = 0;
                    }
                }
            }
        }
        else if (delStage == DEL_HIGHLIGHT_TARGET) {
            // Pause a little to show target highlighting
            delFramesCounter++;
            if (delFramesCounter >= 30) {
                // decide case
                if (!delTargetNode->left && !delTargetNode->right) {
                    // leaf
                    delStage = DEL_SHRINK_REMOVE;
                    animNode = delTargetNode;
                    animProgress = 0.0f;
                }
                else if (delTargetNode->left && delTargetNode->right) {
                    // two-child: find successor
                    auto pr = FindInorderSuccessor(delTargetNode);
                    successorParent = pr.first ? pr.first : delTargetNode;
                    successorNode = pr.second;
                    if (successorNode) {
                        delStage = DEL_HIGHLIGHT_SUCCESSOR;
                        delFramesCounter = 0;
                    }
                    else {
                        // fallback: treat as one-child
                        delStage = DEL_REWIRING;
                    }
                }
                else {
                    // one-child
                    delStage = DEL_MOVE_CHILD_UP;
                    // pick child
                    if (delTargetNode->left) animNode = delTargetNode->left;
                    else animNode = delTargetNode->right;
                    moveStartX = animNode->animX; moveStartY = animNode->animY;
                    moveTargetX = delTargetNode->x; moveTargetY = delTargetNode->y;
                    animProgress = 0.0f;
                }
                delFramesCounter = 0;
            }
        }
        else if (delStage == DEL_HIGHLIGHT_SUCCESSOR) {
            delFramesCounter++;
            if (delFramesCounter >= 30) {
                // start moving successor to target position (visual)
                delStage = DEL_MOVE_SUCCESSOR;
                animNode = successorNode;
                animReplaceNode = delTargetNode;
                moveStartX = successorNode->animX; moveStartY = successorNode->animY;
                moveTargetX = delTargetNode->x; moveTargetY = delTargetNode->y;
                animProgress = 0.0f;
            }
        }
        else if (delStage == DEL_MOVE_SUCCESSOR) {
            animProgress += 1.0f / animDuration;
            if (animProgress > 1.0f) animProgress = 1.0f;
            // linear interpolation of animNode's anim pos to target
            animNode->animX = moveStartX + (moveTargetX - moveStartX) * animProgress;
            animNode->animY = moveStartY + (moveTargetY - moveStartY) * animProgress;
            if (animProgress >= 1.0f) {
                // copy successor value into target node (visual), then remove successor structurally
                delTargetNode->value = successorNode->value; // value copied
                // Now remove successor from tree structurally
                // successorNode has no left child by definition
                // find successor parent properly (may be delTargetNode or deeper)
                // remove successor reference
                // If successorParent == successorNode -> means successor is right child of delTargetNode
                if (successorParent == successorNode) {
                    // special case (shouldn't happen due to our FindInorderSuccessor)
                    ;
                }
                // unlink successor:
                if (successorParent) {
                    if (successorParent->left == successorNode) successorParent->left = successorNode->right;
                    else if (successorParent->right == successorNode) successorParent->right = successorNode->right;
                }
                else {
                    // successorParent null means root? unlikely
                }
                // free successorNode memory pointer (we can't delete while animating; but animation finished)
                DeleteNodePointer(successorNode);
                successorNode = nullptr;
                successorParent = nullptr;
                animNode = nullptr;
                animReplaceNode = nullptr;
                // After structural change, recompute layout and animate nodes to new positions
                RecomputeLayoutAndSnap(root, screenW);
                delStage = DEL_FINALIZE;
                delFramesCounter = 0;
            }
        }
        else if (delStage == DEL_MOVE_CHILD_UP) {
            animProgress += 1.0f / animDuration;
            if (animProgress > 1.0f) animProgress = 1.0f;
            animNode->animX = moveStartX + (moveTargetX - moveStartX) * animProgress;
            animNode->animY = moveStartY + (moveTargetY - moveStartY) * animProgress;
            if (animProgress >= 1.0f) {
                // rewire pointers: replace delTargetNode with animNode in parent's link
                // find parent of delTargetNode
                Node* parent = delTargetParent;
                // If delTargetNode had two children there's other logic; here it's one-child case
                if (parent == nullptr) {
                    // deleting root -> new root is animNode
                    if (delTargetNode->left && delTargetNode->right) {
                        // shouldn't happen
                    }
                    else if (delTargetNode->left) root = delTargetNode->left;
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
                // delete the old target node pointer
                DeleteNodePointer(delTargetNode);
                delTargetNode = nullptr;
                animNode = nullptr;
                // recompute layout
                RecomputeLayoutAndSnap(root, screenW);
                delStage = DEL_FINALIZE;
            }
        }
        else if (delStage == DEL_SHRINK_REMOVE) {
            // shrink animNode down
            if (!animNode) {
                delStage = DEL_FINALIZE;
            }
            else {
                animProgress += 1.0f / (animDuration / 1.5f);
                animNode->radius = 25 * (1.0f - animProgress);
                animNode->color = Fade(RED, 1.0f - animProgress);
                if (animProgress >= 1.0f) {
                    // remove leaf structurally
                    Node* parent = delTargetParent;
                    if (!parent) {
                        // deleting root (only node)
                        DeleteNodePointer(root);
                    }
                    else {
                        if (parent->left == animNode) parent->left = nullptr;
                        else if (parent->right == animNode) parent->right = nullptr;
                        DeleteNodePointer(animNode);
                    }
                    animNode = nullptr;
                    delTargetNode = nullptr;
                    delStage = DEL_FINALIZE;
                }
            }
        }
        else if (delStage == DEL_FINALIZE) {
            // let nodes slide to final positions smoothly for a while
            delFramesCounter++;
            if (delFramesCounter > 20) {
                delStage = DEL_IDLE;
                delTraversalPath.clear();
                delTraversalIndex = 0;
                delFramesCounter = 0;
            }
        }

        // Smooth movement for all nodes to their desired places (when not animating a specific node)
        SmoothMoveAll(root, 0.18f);

        // --- Draw ---
        BeginDrawing();
        ClearBackground(RAYWHITE);

        BeginMode2D(camera);
        // pick highlight node for drawing during traversal
        Node* highlight = nullptr;
        if (delStage == DEL_TRAVERSING && delTraversalIndex < (int)delTraversalPath.size()) {
            highlight = delTraversalPath[delTraversalIndex];
        }
        else if (delStage == DEL_HIGHLIGHT_TARGET && delTargetNode) {
            highlight = delTargetNode;
        }
        else if (delStage == DEL_HIGHLIGHT_SUCCESSOR && successorNode) {
            highlight = successorNode;
        }
        else if (delStage == DEL_MOVE_SUCCESSOR && animNode) {
            highlight = nullptr; // successor is being animated; we'll show special color
        }

        Node* special = nullptr;
        if (delStage == DEL_MOVE_SUCCESSOR && animNode) special = animNode;

        DrawTree(root, highlight, special);

        EndMode2D();

        // UI top
        DrawRectangle(0, 0, screenW, 130, LIGHTGRAY);
        DrawText("BST Visualizer - Insert and Delete (Option C step-by-step replacement)", 20, 18, 22, BLACK);
        DrawText("Click Insert or Delete to focus field. Type number and press Enter.", 20, 46, 18, DARKGRAY);

        // Buttons
        // Insert button
        {
            Color c = CheckCollisionPointRec(mouse, insertBtn) ? GRAY : LIGHTGRAY;
            DrawRectangleRec(insertBtn, c);
            DrawRectangleLines((int)insertBtn.x, (int)insertBtn.y, (int)insertBtn.width, (int)insertBtn.height, BLACK);
            DrawText("Insert", (int)insertBtn.x + 30, (int)insertBtn.y + 8, 20, BLACK);
        }
        // Delete button
        {
            Color c = CheckCollisionPointRec(mouse, deleteBtn) ? GRAY : LIGHTGRAY;
            DrawRectangleRec(deleteBtn, c);
            DrawRectangleLines((int)deleteBtn.x, (int)deleteBtn.y, (int)deleteBtn.width, (int)deleteBtn.height, BLACK);
            DrawText("Delete", (int)deleteBtn.x + 30, (int)deleteBtn.y + 8, 20, BLACK);
        }

        // Input box
        DrawRectangleRec(inputBox, WHITE);
        DrawRectangleLines((int)inputBox.x, (int)inputBox.y, (int)inputBox.width, (int)inputBox.height, BLACK);
        std::string hint = inputFocused ? "" : (deleteMode ? "(delete mode)" : "(insert mode)");
        DrawText(inputText.c_str(), (int)inputBox.x + 8, (int)inputBox.y + 6, 20, BLACK);
        DrawText(hint.c_str(), (int)inputBox.x + 8, (int)(inputBox.y + inputBox.height + 4), 14, DARKGRAY);

        // instructions
        DrawText("Arrow keys to pan, wheel to zoom", 540, 78, 16, DARKGRAY);

        EndDrawing();

        // After drawing, handle mouse clicks that trigger Insert/Delete actions (we needed to draw buttons first)
        if (IsMouseButtonPressed(MOUSE_LEFT_BUTTON)) {
            if (CheckCollisionPointRec(mouse, insertBtn)) {
                inputFocused = true;
                deleteMode = false;
            }
            if (CheckCollisionPointRec(mouse, deleteBtn)) {
                inputFocused = true;
                deleteMode = true;
            }
        }
    }

    // cleanup tree
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
