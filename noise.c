#include <stdio.h>
#include <stdlib.h>

#define SQUARE_WIDTH 50
#define SQUARE_HEIGHT 50

#define GRID_WIDTH 20
#define GRID_HEIGHT 20

#define IMAGE_WIDTH (GRID_WIDTH * SQUARE_WIDTH)
#define IMAGE_HEIGHT (GRID_HEIGHT * SQUARE_HEIGHT)

int data[IMAGE_HEIGHT][IMAGE_WIDTH];

const int UNIT = 32768;

void patch(int grid_i, int grid_j, int a, int b, int c) {
    int centre_i = SQUARE_WIDTH * grid_i;
    int centre_j = SQUARE_HEIGHT * grid_j;
    for (int j = -SQUARE_HEIGHT; j <= SQUARE_HEIGHT; j++) {
        int image_j = (centre_j + j) % IMAGE_HEIGHT;

        int y = -j * UNIT / SQUARE_HEIGHT;
        int qy = (y + UNIT) * (y - UNIT) / UNIT;
        int qqy = qy * qy / UNIT;

        for (int i = -SQUARE_WIDTH; i <= SQUARE_WIDTH; i++) {
            int image_i = (centre_i + i) % IMAGE_WIDTH;

            int x = i * UNIT / SQUARE_WIDTH;
            int qx = (x + UNIT) * (x - UNIT) / UNIT;
            int qqx = qx * qx / UNIT;

            int v = a * x / UNIT + b * y / UNIT + c;
            int z = v * qqx / UNIT * qqy / UNIT;

            data[image_j][image_i] += z;
        }
    }
}

int main() {
    FILE *out = fopen("noise.ppm", "w");

    srand(1);

    for (int j = 0; j < IMAGE_HEIGHT; j++) {
        for (int i = 0; i < IMAGE_WIDTH; i++) {
            data[j][i] = 0;
        }
    }

    for (int j = 1; j <= GRID_HEIGHT; j++) {
        for (int i = 1; i <= GRID_WIDTH; i++) {
            int a = rand() % (2 * UNIT) - UNIT;
            int b = rand() % (2 * UNIT) - UNIT;
            int c = rand() % (2 * UNIT) - UNIT;
            int scale = 20000;
            a = a * scale / UNIT;
            b = b * scale / UNIT;
            c = c * scale / UNIT;
            patch(i, j, a, b, c);
        }
    }

    fprintf(out, "P3 %d %d %d\n", IMAGE_WIDTH, IMAGE_HEIGHT, 255);
    for (int j = 0; j < IMAGE_HEIGHT; j++) {
        for (int i = 0; i < IMAGE_WIDTH; i++) {
            int val = data[j][i] * 255 / UNIT;
            int red = 0, green = 0, blue = 0;

            switch ('r') {
            case 'r':
                if (val < 0) {
                    red = -val;
                } else {
                    blue = val;
                }
                break;
            case 'g':
                if (val < 0) {
                    blue = -val;
                    green = 255 + val;
                } else {
                    red = val;
                    green = 255;
                }
                break;
            case 'w':
                red = (val + 255) / 2;
                green = red;
                blue = red;
                break;
            }

            fprintf(out, "%d %d %d ", red, green, blue);
        }
        fprintf(out, "\n");
    }
}
