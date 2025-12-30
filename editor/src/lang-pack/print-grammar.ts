import { parser } from "./syntax";

/////// MANUAL TEST FILE ///////////
//
// This file should be used for manually testing the grammar only!
//
// This file should **not** be imported anywhere and is hence
// not included in the output build.
//
// Run using `ts-node print-grammar.ts` 
//     see (https://www.npmjs.com/package/ts-node)
//
///////////////////////////////////

const source = `Example example1_1_1 (a b c : ℤ) :
  c | b ⇒ b | a ⇒ True ⇒ c | a.
Proof.
We show both statements.
We show both directions.
Assume that c | b as (i), b | a as (ii) and True as (iii).
By (i) it holds that ∃ n ∈ ℤ, b = n * c.
Obtain such n.
By (i) and (ii) it holds that ∃ m ∈ ℤ, a = m * b.
Obtain such an m.
It holds that c * (n * m) = a.
It suffices to show that ∃ k ∈ ℤ, a = k * c.
Choose k := n*m.
{ Indeed, k ∈ ℤ. }
We conclude that a = k * c.
Qed.`;
const tree = parser.parse(source);
console.log(tree.toString());
