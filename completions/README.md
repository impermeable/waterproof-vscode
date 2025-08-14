## Categories for symbols.
These are used in the symbols panel:

- 0 = lower case greek letters
- 1 = upper case greek letters
- 2 = mathematical symbols
- 3 = arrows
- 4 = number systems
- 5 = super and subscripts
- 99 = Not supposed to show up in symbols panel.

## Syntax to create a snippet template: 
Encapsulate the part that needs to be edited by `${` and `}`.<br>
So,
```json
"label": "Take (*name*) : ((*set*))." 
```
becomes
```json
"template": "Take ${(*name*)} : (${(*set*)}).",
```