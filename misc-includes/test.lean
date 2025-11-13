
-- Basic func
def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n+1 => (n+1) * factorial n

-- Test 
#eval factorial 5

/- begin details : Hint -/
blah blah
/- end -/

/- begin input -/
-- Try implementation
blah blah
/- end -/