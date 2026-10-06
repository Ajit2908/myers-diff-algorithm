import java.io.BufferedOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

public class Main {

    // Holds line byte boundaries (starts, lens) within the raw byte buffer.
    static class RawLines {
        final byte[] data;
        final int[] starts;
        final int[] lens;
        final int count;

        RawLines(byte[] data, int[] starts, int[] lens, int count) {
            this.data = data;
            this.starts = starts;
            this.lens = lens;
            this.count = count;
        }
    }

    // Maps unique line byte sequences to integer IDs so Myers can compare
    // lines with fast O(1) integer equality instead of byte-by-byte comparisons.
    static class LineTable {
        private final int mask;
        private final int[] head;
        private final int[] next;
        private final byte[] source;
        private final int[] start;
        private final int[] len;
        private final int[] id;
        private int count = 0;

        LineTable(int capacity) {
            int cap = 16;
            while (cap < capacity * 2) {
                cap <<= 1;
            }
            this.mask = cap - 1;
            this.head = new int[cap];
            Arrays.fill(this.head, -1);
            this.next = new int[capacity + 1];
            this.source = new byte[capacity + 1];
            this.start = new int[capacity + 1];
            this.len = new int[capacity + 1];
            this.id = new int[capacity + 1];
        }

        int getOrAdd(byte src, byte[] data, int s, int l, byte[] dataA, byte[] dataB) {
            int h = 1;
            for (int i = 0; i < l; i++) {
                h = 31 * h + data[s + i];
            }
            int bucket = (h ^ (h >>> 16)) & mask;

            int curr = head[bucket];
            while (curr != -1) {
                if (len[curr] == l) {
                    byte[] existingData = (source[curr] == 0) ? dataA : dataB;
                    if (Arrays.equals(data, s, s + l, existingData, start[curr], start[curr] + l)) {
                        return id[curr];
                    }
                }
                curr = next[curr];
            }

            int newIdx = count++;
            source[newIdx] = src;
            start[newIdx] = s;
            len[newIdx] = l;
            id[newIdx] = newIdx;
            next[newIdx] = head[bucket];
            head[bucket] = newIdx;
            return newIdx;
        }
    }

    // Represents a diagonal match segment (snake) starting at (x, y) of length len.
    static class Snake {
        final int x;
        final int y;
        final int len;

        Snake(int x, int y, int len) {
            this.x = x;
            this.y = y;
            this.len = len;
        }
    }

    // Splits raw bytes on '\n' (0x0A), preserving '\r' (CRLF vs LF distinction).
    // Drops any trailing empty piece so a final newline does not create a false extra line.
    static RawLines parseLines(byte[] data) {
        if (data == null || data.length == 0) {
            return new RawLines(data, new int[0], new int[0], 0);
        }

        int n = data.length;
        int lineCount = 0;
        int start = 0;
        for (int i = 0; i < n; i++) {
            if (data[i] == 0x0A) {
                lineCount++;
                start = i + 1;
            }
        }
        if (start < n) {
            lineCount++;
        }

        int[] starts = new int[lineCount];
        int[] lens = new int[lineCount];
        int idx = 0;
        start = 0;
        for (int i = 0; i < n; i++) {
            if (data[i] == 0x0A) {
                starts[idx] = start;
                lens[idx] = i - start;
                idx++;
                start = i + 1;
            }
        }
        if (start < n) {
            starts[idx] = start;
            lens[idx] = n - start;
            idx++;
        }

        return new RawLines(data, starts, lens, lineCount);
    }

    // Writes a diff line: prefix (' ' keep, '-' delete, '+' insert) + original bytes + '\n'.
    private static void writeLine(OutputStream out, byte prefix, byte[] data, int start, int len) throws IOException {
        out.write(prefix);
        if (len > 0) {
            out.write(data, start, len);
        }
        out.write(0x0A);
    }

    private static void writeHighlightLine(OutputStream out, String hl) throws IOException {
        byte[] bytes = hl.getBytes(StandardCharsets.UTF_8);
        out.write(bytes);
        out.write(0x0A);
    }

    // Formats changed indices into 0-based half-open ranges "start-end" (e.g. 3-5).
    // Merges adjacent/touching changes, and outputs "." if no characters changed.
    private static String formatRanges(boolean[] changed) {
        if (changed == null || changed.length == 0) {
            return ".";
        }
        StringBuilder sb = new StringBuilder();
        boolean first = true;
        int i = 0;
        while (i < changed.length) {
            if (changed[i]) {
                int start = i;
                while (i < changed.length && changed[i]) {
                    i++;
                }
                if (!first) {
                    sb.append(',');
                }
                sb.append(start).append('-').append(i);
                first = false;
            } else {
                i++;
            }
        }
        return first ? "." : sb.toString();
    }

    // Computes Part B character diff using Unicode code points so emojis count as 1 character.
    // '\r' is retained and counts as a character; newlines are excluded.
    private static String computeHighlight(byte[] dataA, int sA, int lA, byte[] dataB, int sB, int lB) {
        String strA = new String(dataA, sA, lA, StandardCharsets.UTF_8);
        String strB = new String(dataB, sB, lB, StandardCharsets.UTF_8);
        int[] cpA = strA.codePoints().toArray();
        int[] cpB = strB.codePoints().toArray();

        int nA = cpA.length;
        int nB = cpB.length;

        int p = 0;
        while (p < nA && p < nB && cpA[p] == cpB[p]) {
            p++;
        }

        int s = 0;
        while (s < nA - p && s < nB - p && cpA[nA - 1 - s] == cpB[nB - 1 - s]) {
            s++;
        }

        boolean[] changedA = new boolean[nA];
        boolean[] changedB = new boolean[nB];

        int nTrimmed = nA - p - s;
        int mTrimmed = nB - p - s;

        if (nTrimmed == 0 && mTrimmed == 0) {
            // Identical lines
        } else if (nTrimmed == 0) {
            for (int j = p; j < nB - s; j++) {
                changedB[j] = true;
            }
        } else if (mTrimmed == 0) {
            for (int i = p; i < nA - s; i++) {
                changedA[i] = true;
            }
        } else {
            int[] aTrimmed = new int[nTrimmed];
            System.arraycopy(cpA, p, aTrimmed, 0, nTrimmed);
            int[] bTrimmed = new int[mTrimmed];
            System.arraycopy(cpB, p, bTrimmed, 0, mTrimmed);

            List<Snake> snakes = runMyers(aTrimmed, bTrimmed);

            boolean[] inSnakeA = new boolean[nTrimmed];
            boolean[] inSnakeB = new boolean[mTrimmed];
            for (Snake snake : snakes) {
                for (int k = 0; k < snake.len; k++) {
                    inSnakeA[snake.x + k] = true;
                    inSnakeB[snake.y + k] = true;
                }
            }
            for (int i = 0; i < nTrimmed; i++) {
                if (!inSnakeA[i]) {
                    changedA[p + i] = true;
                }
            }
            for (int j = 0; j < mTrimmed; j++) {
                if (!inSnakeB[j]) {
                    changedB[p + j] = true;
                }
            }
        }

        String rangesA = formatRanges(changedA);
        String rangesB = formatRanges(changedB);

        return "? " + rangesA + " | " + rangesB;
    }

    // Overall pipeline: read raw bytes -> parse lines -> intern to IDs -> trim prefix/suffix
    // -> run Myers diff -> emit change blocks (delete-first) -> optionally compute highlights.
    public static void main(String[] args) {
        if (args.length != 3 || (!args[0].equals("lines") && !args[0].equals("highlight"))) {
            System.err.println("Usage: Main <lines|highlight> <fileA> <fileB>");
            System.exit(2);
        }

        boolean highlight = args[0].equals("highlight");
        String pathA = args[1];
        String pathB = args[2];

        byte[] dataA = null;
        byte[] dataB = null;

        try {
            Path pA = Paths.get(pathA);
            Path pB = Paths.get(pathB);
            dataA = Files.readAllBytes(pA);
            dataB = Files.readAllBytes(pB);
        } catch (Exception e) {
            System.err.println("Error reading input files: " + e.getMessage());
            System.exit(2);
        }

        RawLines rawA = parseLines(dataA);
        RawLines rawB = parseLines(dataB);

        int totalLines = rawA.count + rawB.count;
        LineTable table = new LineTable(totalLines);
        int[] aIds = new int[rawA.count];
        for (int i = 0; i < rawA.count; i++) {
            aIds[i] = table.getOrAdd((byte) 0, rawA.data, rawA.starts[i], rawA.lens[i], dataA, dataB);
        }
        int[] bIds = new int[rawB.count];
        for (int j = 0; j < rawB.count; j++) {
            bIds[j] = table.getOrAdd((byte) 1, rawB.data, rawB.starts[j], rawB.lens[j], dataA, dataB);
        }

        int p = 0;
        while (p < rawA.count && p < rawB.count && aIds[p] == bIds[p]) {
            p++;
        }

        int s = 0;
        while (s < rawA.count - p && s < rawB.count - p && aIds[rawA.count - 1 - s] == bIds[rawB.count - 1 - s]) {
            s++;
        }

        int nTrimmed = rawA.count - p - s;
        int mTrimmed = rawB.count - p - s;

        try (OutputStream out = new BufferedOutputStream(System.out, 65536)) {
            for (int i = 0; i < p; i++) {
                writeLine(out, (byte) ' ', rawA.data, rawA.starts[i], rawA.lens[i]);
            }

            if (nTrimmed == 0 && mTrimmed == 0) {
                // Fully identical or covered by prefix/suffix
            } else if (nTrimmed == 0) {
                for (int j = p; j < rawB.count - s; j++) {
                    writeLine(out, (byte) '+', rawB.data, rawB.starts[j], rawB.lens[j]);
                }
            } else if (mTrimmed == 0) {
                for (int i = p; i < rawA.count - s; i++) {
                    writeLine(out, (byte) '-', rawA.data, rawA.starts[i], rawA.lens[i]);
                }
            } else {
                int[] aTrimmed = new int[nTrimmed];
                System.arraycopy(aIds, p, aTrimmed, 0, nTrimmed);
                int[] bTrimmed = new int[mTrimmed];
                System.arraycopy(bIds, p, bTrimmed, 0, mTrimmed);

                List<Snake> snakes = runMyers(aTrimmed, bTrimmed);

                int currX = 0;
                int currY = 0;
                for (Snake snake : snakes) {
                    int delCount = snake.x - currX;

                    // Delete-first rule: emit all '-' before any '+' in a change block
                    for (int x = currX; x < snake.x; x++) {
                        writeLine(out, (byte) '-', rawA.data, rawA.starts[p + x], rawA.lens[p + x]);
                    }
                    for (int y = currY; y < snake.y; y++) {
                        writeLine(out, (byte) '+', rawB.data, rawB.starts[p + y], rawB.lens[p + y]);
                        if (highlight) {
                            int pairIdx = y - currY;
                            // Pair j-th deletion with j-th insertion in this change block
                            if (pairIdx < delCount) {
                                int oldLineIdx = p + currX + pairIdx;
                                int newLineIdx = p + y;
                                String hl = computeHighlight(rawA.data, rawA.starts[oldLineIdx], rawA.lens[oldLineIdx],
                                                             rawB.data, rawB.starts[newLineIdx], rawB.lens[newLineIdx]);
                                writeHighlightLine(out, hl);
                            }
                        }
                    }
                    for (int i = 0; i < snake.len; i++) {
                        writeLine(out, (byte) ' ', rawA.data, rawA.starts[p + snake.x + i], rawA.lens[p + snake.x + i]);
                    }
                    currX = snake.x + snake.len;
                    currY = snake.y + snake.len;
                }

                int delCount = nTrimmed - currX;
                for (int x = currX; x < nTrimmed; x++) {
                    writeLine(out, (byte) '-', rawA.data, rawA.starts[p + x], rawA.lens[p + x]);
                }
                for (int y = currY; y < mTrimmed; y++) {
                    writeLine(out, (byte) '+', rawB.data, rawB.starts[p + y], rawB.lens[p + y]);
                    if (highlight) {
                        int pairIdx = y - currY;
                        if (pairIdx < delCount) {
                            int oldLineIdx = p + currX + pairIdx;
                            int newLineIdx = p + y;
                            String hl = computeHighlight(rawA.data, rawA.starts[oldLineIdx], rawA.lens[oldLineIdx],
                                                         rawB.data, rawB.starts[newLineIdx], rawB.lens[newLineIdx]);
                            writeHighlightLine(out, hl);
                        }
                    }
                }
            }

            for (int i = rawA.count - s; i < rawA.count; i++) {
                writeLine(out, (byte) ' ', rawA.data, rawA.starts[i], rawA.lens[i]);
            }

            out.flush();
        } catch (IOException e) {
            System.err.println("Error writing diff output: " + e.getMessage());
            System.exit(2);
        }
    }

    /*
     * Myers' O(ND) greedy diff algorithm:
     * - Edit graph: horizontal step (x+1, y) = delete from A, vertical step (x, y+1) = insert from B.
     * - Diagonal k = x - y: delete moves from k-1 to k; insert moves from k+1 to k.
     * - v[offset + k] stores the furthest x reached on diagonal k at edit distance d.
     * - Snake: greedily extends along the diagonal (x+1, y+1) while elements match (free cost).
     * - Iterating d = 0, 1, 2... guarantees finding the minimal edit distance first.
     * - vHistory records active slices per step d to backtrack the path without copying full arrays.
     */
    private static List<Snake> runMyers(int[] a, int[] b) {
        int n = a.length;
        int m = b.length;
        int maxD = n + m;
        int offset = maxD;

        int[] v = new int[2 * maxD + 1];
        Arrays.fill(v, 0);

        List<int[]> vHistory = new ArrayList<>();

        int x0 = 0;
        while (x0 < n && x0 < m && a[x0] == b[x0]) {
            x0++;
        }
        v[offset] = x0;
        vHistory.add(new int[]{x0});

        int finalD = 0;
        if (x0 < n || x0 < m) {
            boolean found = false;
            for (int d = 1; d <= maxD; d++) {
                int[] snap = new int[d + 1];
                for (int k = -d; k <= d; k += 2) {
                    boolean down = (k == -d || (k != d && v[offset + k - 1] < v[offset + k + 1]));
                    int x = down ? v[offset + k + 1] : v[offset + k - 1] + 1;
                    int y = x - k;

                    while (x < n && y < m && a[x] == b[y]) {
                        x++;
                        y++;
                    }

                    v[offset + k] = x;
                    snap[(k + d) / 2] = x;

                    if (x >= n && y >= m) {
                        found = true;
                        finalD = d;
                        break;
                    }
                }
                vHistory.add(snap);
                if (found) {
                    break;
                }
            }
        }

        // Backtrack through vHistory from finalD down to 1 to recover matching snakes
        List<Snake> snakes = new ArrayList<>();
        int currX = n;
        int currY = m;
        int currK = n - m;

        for (int d = finalD; d >= 1; d--) {
            int[] prevSnap = vHistory.get(d - 1);
            boolean down = (currK == -d || (currK != d && prevSnap[(currK + d - 2) / 2] < prevSnap[(currK + d) / 2]));
            int prevK = down ? currK + 1 : currK - 1;
            int xStart = down ? prevSnap[(currK + d) / 2] : prevSnap[(currK + d - 2) / 2];
            int yStart = xStart - prevK;
            int xMid = down ? xStart : xStart + 1;
            int yMid = down ? yStart + 1 : yStart;

            int snakeLen = currX - xMid;
            if (snakeLen > 0) {
                snakes.add(new Snake(xMid, yMid, snakeLen));
            }

            currX = xStart;
            currY = yStart;
            currK = prevK;
        }

        if (currX > 0) {
            snakes.add(new Snake(0, 0, currX));
        }

        Collections.reverse(snakes);
        return snakes;
    }
}
