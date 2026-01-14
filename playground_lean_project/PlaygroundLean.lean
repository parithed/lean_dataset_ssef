set_option maxHeartbeats 0

-- A small playground of theorems for MCTS + LLM experiments.
-- All of these are in core Lean (no Mathlib / Std imports).

--------------------------------
-- Basic equalities on Nat
--------------------------------

theorem t1 : 1 = 1 := rfl

theorem t2 (n : Nat) : n = n := rfl

theorem t3 (n : Nat) : n + 0 = n := by
  simp  -- uses Nat.add_zero

theorem t4 (n : Nat) : 0 + n = n := by
  simp  -- uses Nat.zero_add

theorem t5 (n : Nat) : n * 1 = n := by
  simp  -- uses Nat.mul_one

theorem t6 (n : Nat) : 1 * n = n := by
  simp  -- uses Nat.one_mul

theorem t7 (n : Nat) : n * 0 = 0 := by
  simp  -- uses Nat.mul_zero

theorem t8 (n : Nat) : 0 * n = 0 := by
  simp  -- uses Nat.zero_mul

--------------------------------
-- Commutativity / associativity
--------------------------------

theorem t9  (a b : Nat) : a + b = b + a := by
  simpa using Nat.add_comm a b

theorem t10 (a b c : Nat) : (a + b) + c = a + (b + c) := by
  simpa using Nat.add_assoc a b c

theorem t11 (a b : Nat) : a * b = b * a := by
  simpa using Nat.mul_comm a b

theorem t12 (a b c : Nat) : (a * b) * c = a * (b * c) := by
  simpa using Nat.mul_assoc a b c

--------------------------------
-- Distributivity and rearrangements
--------------------------------

theorem t13 (a b c : Nat) : a * (b + c) = a * b + a * c := by
  simpa using Nat.mul_add a b c

theorem t14 (a b c : Nat) : (a + b) * c = a * c + b * c := by
  simpa using Nat.add_mul a b c

theorem t15 (a b c d : Nat) :
    (a + b) + (c + d) = a + (b + c) + d := by
  -- just reshuffle with associativity and commutativity
  calc
    (a + b) + (c + d)
        = a + b + (c + d) := by
          simp [Nat.add_assoc]
    _   = a + (b + (c + d)) := by
          simp [Nat.add_assoc]
    _   = a + ((b + c) + d) := by
          simp [Nat.add_assoc]
    _   = a + (b + c) + d := by
          simp [Nat.add_assoc]

--------------------------------
-- Simple propositional logic
--------------------------------

theorem t16 (p : Prop) (hp : p) : p := hp

theorem t17 (p q : Prop) (h : p ∧ q) : p := h.left

theorem t18 (p q : Prop) (h : p ∧ q) : q := h.right

theorem t19 (p q : Prop) (hp : p) (hq : q) : p ∧ q := And.intro hp hq

theorem t20 (p q : Prop) (h : p ∧ q) : q ∧ p := And.intro h.right h.left

theorem t21 (p q r : Prop) (h₁ : p → q) (h₂ : q → r) (hp : p) : r :=
  h₂ (h₁ hp)
