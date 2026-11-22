# P1 Report – Department Assignment Puzzle

**Group ID:** 61

## P1.b – Number of Solutions

Using `count_solutions([1,2,3,4,5,6,7,8], N)`, we obtained:

**N = 3**

This means the original eight clues do not uniquely determine the department, favorite language and project preference of every friend. Three different complete assignments satisfy all eight clues.

## P1.c – Repairing the Puzzle

We introduced the following additional clue:

**Clue 9:** The friend working in the design department prefers embedded projects.

The clue does not mention any friend by name and refers to a person only through attribute values.

After adding Clue 9, we executed:

`count_solutions([1,2,3,4,5,6,7,8,9], N)`

**N = 1**

Therefore, the additional clue eliminates two of the three original solutions and makes the puzzle uniquely solvable.

## Testing

The P1 test suite completed successfully:

**66 tests passed, 0 failed.**

The tests covered candidate generation, uniqueness, clue correctness, solution counting, the additional clue and the required output format of `main/0`.