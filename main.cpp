// bst_visualizer_fixed.cpp
// Binary Search Tree Visualizer (Insert button + input + highlight + red->blue final)
#include "raylib.h"
#include <string>
#include <vector>
#include <cmath>

// ---------- Node and BST structures ----------
struct Node {
    int value;
    Node* left;
    Node* right;
    float x, y;
    Color color;
    Node(int v, float _x, float _y) {
        value = v;
        left = right = nullptr;
        x = _x; y = _y;
        color = RED; // newly created node color
    }
};

class BST {
public:
    Node* root;
    BST() { root = nullptr; }

    // recursive draw
    void Draw(Node* n, Node* highlight) {
        if (!n) return;
        if (n->left) DrawLine(n->x, n->y, n->left->x, n->left->y, BLACK);
        if (n->right) DrawLine(n->x, n->y, n->right->x, n->right->y, BLACK);

        Color fill = n->color;
        if (n == highlight) {
            // draw highlighted circle slightly larger to show emphasis
            DrawCircle(n->x, n->y, 30, YELLOW);
            DrawCircle(n->x, n->y, 25, fill);
            DrawCircleLines(n->x, n->y, 30, DARKBLUE);
        }
        else {
            DrawCircle(n->x, n->y, 25, fill);
            DrawCircleLines(n->x, n->y, 25, DARKBLUE);
        }
        DrawText(std::to_string(n->value).c_str(), (int)(n->x - 10), (int)(n->y - 10), 20, BLACK);

        Draw(n->left, highlight);
        Draw(n->right, highlight);
    }
};

// ---------- Globals for visualizer state ----------
static BST tree;
static Node* highlightNode = nullptr;      // currently visited node during traversal
static Node* newlyInserted = nullptr;      // reference to the node just created (red -> blue)
static int finalizeCountdown = 0;          // frames until newlyInserted turns skyblue

// Insertion-as-state variables
static bool traversing = false;
static std::vector<Node*> traversalPath;   // nodes visited in order
static int traversalIndex = 0;
static int framesSinceStep = 0;
static const int FRAMES_PER_STEP = 10;     // speed of traversal highlighting
static int pendingValue = 0;               // value requested to insert
static bool pendingExists = false;
static float newNodeX = 0, newNodeY = 0;
static Node* newNodeParent = nullptr;
static bool newNodeIsLeft = false;

// ---------- Helper to start insertion traversal (non-blocking) ----------
void StartInsertion(int value, int screenW) {
    traversalPath.clear();
    traversalIndex = 0;
    framesSinceStep = 0;
    traversing = true;
    pendingValue = value;
    pendingExists = true;
    highlightNode = nullptr;
    newNodeParent = nullptr;

    // simulate traversal to collect nodes and compute final position
    Node* cur = tree.root;
    float x = screenW / 2.0f;
    float y = 80.0f;
    float offset = 200.0f;
    Node* parent = nullptr;
    bool isLeft = false;

    while (cur != nullptr) {
        traversalPath.push_back(cur);
        parent = cur;
        if (value < cur->value) {
            // go left
            x = cur->x - offset;
            y = cur->y + 80.0f;
            cur = cur->left;
            isLeft = true;
        }
        else {
            // go right (duplicates go to right)
            x = cur->x + offset;
            y = cur->y + 80.0f;
            cur = cur->right;
            isLeft = false;
        }
        offset *= 0.6f;
    }

    // if root is null then we'll create root at center
    if (parent == nullptr) {
        newNodeParent = nullptr;
        newNodeX = x;
        newNodeY = y;
        newNodeIsLeft = false;
    }
    else {
        newNodeParent = parent;
        newNodeX = x;
        newNodeY = y;
        newNodeIsLeft = isLeft;
    }
}

// ---------- Attach the new node to the BST (called when traversal finished) ----------
void AttachNewNode() {
    // create node at computed position
    Node* n = new Node(pendingValue, newNodeX, newNodeY);
    if (newNodeParent == nullptr) {
        tree.root = n;
    }
    else {
        if (newNodeIsLeft) newNodeParent->left = n;
        else newNodeParent->right = n;
    }
    newlyInserted = n;
    finalizeCountdown = 60; // show red for 60 frames (~1 second at 60 fps)
}

// ---------- Basic UI button helper ----------
bool UIBtn(const Rectangle& r, const char* label) {
    Vector2 m = GetMousePosition();
    bool hover = CheckCollisionPointRec(m, r);
    Color c = hover ? GRAY : LIGHTGRAY;
    DrawRectangleRec(r, c);
    DrawRectangleLines((int)r.x, (int)r.y, (int)r.width, (int)r.height, BLACK);
    DrawText(label, (int)r.x + 10, (int)r.y + 8, 20, BLACK);
    if (hover && IsMouseButtonPressed(MOUSE_LEFT_BUTTON)) return true;
    return false;
}

// ---------- Main ----------
int main() {
    const int screenW = 1400;
    const int screenH = 900;
    InitWindow(screenW, screenH, "BST Visualizer - Fixed (Insert + Highlight + Red->Blue)");
    SetTargetFPS(60);

    // UI elements
    Rectangle inputBox = { 240, 70, 140, 36 };
    Rectangle insertBtn = { 20, 70, 200, 40 };
    std::string inputText = "";
    bool inputFocused = false;

    Camera2D camera = { 0 };
    camera.target = { 0, 0 };
    camera.offset = { 0, 0 };
    camera.zoom = 1.0f;

    while (!WindowShouldClose()) {
        // ---- UI interaction: focus on input box ----
        Vector2 mouse = GetMousePosition();
        if (CheckCollisionPointRec(mouse, inputBox) && IsMouseButtonPressed(MOUSE_LEFT_BUTTON)) {
            inputFocused = true;
        }
        if (!CheckCollisionPointRec(mouse, inputBox) && IsMouseButtonPressed(MOUSE_LEFT_BUTTON)) {
            inputFocused = false;
        }

        // typing into input
        if (inputFocused) {
            int key = GetCharPressed();
            while (key > 0) {
                if ((key >= '0' && key <= '9') && inputText.size() < 7) inputText.push_back((char)key);
                key = GetCharPressed();
            }
            if (IsKeyPressed(KEY_BACKSPACE) && !inputText.empty()) inputText.pop_back();
            if (IsKeyPressed(KEY_ENTER) && !inputText.empty() && !traversing) {
                // start insertion
                int v = std::stoi(inputText);
                StartInsertion(v, screenW);
                inputText.clear();
            }
        }

        // Insert button pressed
        if (UIBtn(insertBtn, "Insert Value") && !inputText.empty() && !traversing) {
            int v = std::stoi(inputText);
            StartInsertion(v, screenW);
            inputText.clear();
        }

        // camera controls
        if (IsKeyDown(KEY_RIGHT)) camera.target.x += 8;
        if (IsKeyDown(KEY_LEFT))  camera.target.x -= 8;
        if (IsKeyDown(KEY_UP))    camera.target.y -= 8;
        if (IsKeyDown(KEY_DOWN))  camera.target.y += 8;
        camera.zoom += GetMouseWheelMove() * 0.05f;
        if (camera.zoom < 0.2f) camera.zoom = 0.2f;
        if (camera.zoom > 3.0f) camera.zoom = 3.0f;

        // ---- Traversal state machine (non-blocking over frames) ----
        if (traversing) {
            // if traversal path empty -> immediately attach (this is root case)
            if (traversalPath.empty()) {
                AttachNewNode();
                traversing = false;
                pendingExists = false;
                highlightNode = nullptr;
            }
            else {
                framesSinceStep++;
                if (framesSinceStep >= FRAMES_PER_STEP) {
                    framesSinceStep = 0;

                    if (traversalIndex < (int)traversalPath.size()) {
                        highlightNode = traversalPath[traversalIndex];
                        traversalIndex++;
                    }
                    // finished visiting all nodes -> attach
                    if (traversalIndex >= (int)traversalPath.size()) {
                        // brief pause so user sees last highlight before insertion
                        // next frame attach
                        if (framesSinceStep == 0) {
                            AttachNewNode();
                            traversing = false;
                            pendingExists = false;
                            highlightNode = nullptr;
                        }
                    }
                }
            }
        }

        // finalize countdown for newly inserted node (red -> skyblue)
        if (newlyInserted && finalizeCountdown > 0) {
            finalizeCountdown--;
            if (finalizeCountdown == 0) {
                newlyInserted->color = SKYBLUE;
                newlyInserted = nullptr;
            }
        }

        // ---- Draw ----
        BeginDrawing();
        ClearBackground(RAYWHITE);

        BeginMode2D(camera);

        tree.Draw(tree.root, highlightNode);

        EndMode2D();

        // UI top bar
        DrawRectangle(0, 0, screenW, 130, LIGHTGRAY);
        DrawText("BST Visualizer - Fixed", 20, 18, 28, BLACK);
        DrawText("Enter value and click Insert or press Enter:", 240, 46, 18, BLACK);

        // input box
        DrawRectangleRec(inputBox, WHITE);
        DrawRectangleLines((int)inputBox.x, (int)inputBox.y, (int)inputBox.width, (int)inputBox.height, BLACK);
        DrawText(inputText.c_str(), (int)inputBox.x + 8, (int)inputBox.y + 6, 20, BLACK);

        // instructions
        DrawText("Arrow keys to pan, mouse wheel to zoom", 420, 80, 16, DARKGRAY);

        EndDrawing();
    }

    CloseWindow();
    return 0;
}
