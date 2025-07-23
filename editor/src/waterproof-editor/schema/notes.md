# Waterproof Documents

A WaterproofEditor document (`WaterproofDoc`) looks as follows:

```
WaterproofDoc   = ( InputArea
                | Hint
                | Markdown
                | MathDisplay
                | Code )*

InputArea       = Containerizable*
Hint            = Containerizable*

Containerizable = Markdown | MathDisplay | Code

Markdown        = text*
MathDisplay     = text*
Code            = text*
```

# ProseMirror
The schema `WaterproofSchema` defined in [`./schema.ts`](./schema.ts) follows from the above grammar.
