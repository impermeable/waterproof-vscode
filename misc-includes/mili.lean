/-
  TestPlayground.lean
  A small Lean 4 playground file to exercise:
  - syntax highlighting
  - go-to definition
  - diagnostics (type errors, incomplete proofs)
  - hover info, #check, #eval
-/

import Std

namespace TestPlayground

/-! ## Basic definitions -/

def double (n : Nat) : Nat :=
  n * 2

def triple (n : Nat) : Nat :=
  n * 3

def square (n : Nat) : Nat :=
  n * n

#check double
#check triple
#check square

#eval double 10
#eval triple 7
#eval square 12

/-! ## Simple theorem with a proof -/

theorem double_zero : double 0 = 0 := by
  -- unfold definition
  unfold double
  -- `simp` can close this
  simp

theorem double_add (m n : Nat) :
    double (m + n) = double m + double n := by
  unfold double
  -- `Nat.mul_add` can help
  -- m * 2 = 2 * m but we wrote `n * 2`, so rewrite:
  have h1 : (m + n) * 2 = 2 * (m + n) := by
    simp [Nat.mul_comm]
  have h2 : m * 2 = 2 * m := by
    simp [Nat.mul_comm]
  have h3 : n * 2 = 2 * n := by
    simp [Nat.mul_comm]
  -- use the rewrites
  simpa [h1, h2, h3, Nat.add_mul, Nat.mul_add] using
    (show 2 * (m + n) = 2 * m + 2 * n from by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_add])

/-! ## A small structure and lemma -/

structure Point where
  x : Int
  y : Int
deriving Repr, DecidableEq

def origin : Point :=
  ⟨0, 0⟩

def add (p q : Point) : Point :=
  ⟨p.x + q.x, p.y + q.y⟩

#check Point
#check origin
#check add

example : add origin origin = origin := by
  -- unfold everything and simplify
  simp [add, origin, Point.mk.injEq]

/-! ## Using lists and `simp` -/

def sumList (xs : List Nat) : Nat :=
  xs.foldl (fun acc n => acc + n) 0

#eval sumList [1, 2, 3, 4, 5]  -- expect 15

theorem sumList_nil :
    sumList [] = 0 := by
  simp [sumList]

theorem sumList_singleton (n : Nat) :
    sumList [n] = n := by
  simp [sumList]

/-! ## An intentionally incomplete proof (to test holes / sorry) -/

theorem square_nonneg (n : Int) :
    0 ≤ n * n := by
  -- Try replacing `sorry` with an actual proof to test editing
  have : n * n = (Int.natAbs n) * (Int.natAbs n) := by
    -- nontrivial lemma, leave as sorry on purpose
    sorry
  -- after filling the above, you can finish with:
  --   simpa [this] using Int.mul_self_nonneg (Int.natAbs n)
  sorry

/-! ## An obvious contradiction example -/

example (h₁ : p ∧ q) : p := by
  have : p := h₁.left
  exact this

example (h : p ∧ q) : q := by
  exact h.right

/-! ## A small inductive type -/

inductive Color
  | red
  | green
  | blue
  deriving Repr, DecidableEq

open Color

def invert : Color → Color
  | red   => blue
  | blue  => red
  | green => green

#eval invert red
#eval invert green
#eval invert blue

/-! ## A type error on purpose (to test diagnostics) -/
/- Uncomment this block if you want a type error in the file:

#eval "oops" + 1

-/

/-! ## A syntax error on purpose (to test parser)
    Uncomment to see parsing diagnostics:

-- def broken (n : Nat) := (n + ) 1

-/

end TestPlayground
