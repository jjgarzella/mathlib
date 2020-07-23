/-
Copyright (c) 2020 Jack J Garzella. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack J Garzella
-/
import .splitting_field
import tactic.interval_cases

open polynomial



noncomputable theory
universes u v
variables {α : Type u} {β : Type v}
variables [field α] [field β]
variables {i : α →+* β} (hi : function.injective i)



set_option pp.coercions true

-- #check function.injective.decidable_eq

lemma irreducible_factors_degree_lt_of_not_irreducible
  {f : polynomial α} (hf : ¬ irreducible (map i f)) :
  ∀ {g : polynomial β}, irreducible g → g ∣ f.map i → degree g < degree f :=
begin
intros g hg g_dvd,
by_contradiction hgf,
have ge_of_not_le : ∀ a b : ℕ, ¬ a < b → b ≤ a,
  exact λ {a b : ℕ}, not_lt.mp,
have ge_of_not_le_with_bot : ∀ a b : ℕ,
    ¬ (a : with_bot ℕ) < b → (b : with_bot ℕ) ≤ a,
  by sorry,
have g_nat : ∃ n : ℕ, degree g = some n,
  by sorry,
have f_nat : ∃ m : ℕ, degree f = some m,
  by sorry,
-- exists.elim the nats...
-- use ge_of_not_le or some flavor to say that degree degree f ≤ degree g
-- exact ge_of_not_le_with_bot n (degree f) hgf
sorry
end

lemma splits_of_degree_two_not_irreducible {f : polynomial α}
  (hf : ¬ irreducible (map i f)) (degree_f_two : degree f = 2) : splits i f :=
begin
unfold splits,
refine or.inr _,
intros g hg g_dvd,
have degree_g_le_degree_f : degree g < degree f,
  from irreducible_factors_degree_lt_of_not_irreducible hf hg g_dvd,
let n := (degree g),
sorry--interval_cases n,
end




--#check degree_eq_zero_of_is_unit
--#check of_irreducible_mul

example (a b : with_bot ℕ) : (a < b) → (a ≠ b) :=
ne_of_lt

lemma not_irreducible_of_degree_lt_div {f : polynomial α}
    {g : polynomial α} (hg : 0 < degree g) (hgf : degree g < degree f)
    (g_dvd_f : g ∣ f) : ¬ irreducible f :=
assume f_irred,
begin
intros,
have hf : ∀ h : polynomial α, h ∣ f ↔ ∃ j, f = h * j,
  from by { intros, refl },
have g_not_unit : ¬ is_unit g,
  from by { by_contradiction hgg,
            have hgg' : degree g = 0,
              from degree_eq_zero_of_is_unit hgg,
            have hgg'' : degree g ≠ 0, -- this shouldn't be necessary
              by exact (ne.symm (ne_of_lt hg)), -- in a perfect world
            contradiction, },
have f_prod : ∃ j, f = g * j,
  from iff.elim_left (hf g) g_dvd_f,
exact exists.elim f_prod (λ j,
  begin
  intro hj,
  have mul_irreducible : irreducible (g * j),
    from by { rw hj at f_irred, assumption },
  have g_or_j_unit : is_unit g ∨ is_unit j,
    from of_irreducible_mul mul_irreducible,
  have j_not_unit : ¬ is_unit j,
    from sorry, -- some degree theorem in polynomial.lean, will use hgf
  exact g_or_j_unit.elim
          (by { intros, contradiction })
          (by { intros, contradiction })
  end)
end

include hi
lemma not_irreducible_of_root {f : polynomial α} {b : β}
    (hf: 1 < degree f) (root : is_root (map i f) b) :
    ¬ irreducible (map i f) :=
begin
have X_sub_C_dvd : (X - C b) ∣ (map i f),
  from (iff.elim_right dvd_iff_is_root) root,
have degree_one_X_sub_C : degree (X - C b) = 1,
  { have hXb : degree (X ^ 1 - C b) = 1,
      from degree_X_pow_sub_C zero_lt_one b,
    have hX : (X : polynomial β) = X ^ 1,
      by ring_exp,
    rw ←hX at hXb,
    assumption }, -- by const_polynomial
    -- const_polynomial is a tactic I hope to write that
    -- gives proves that explicit constant polynomials
    -- are {monic, degree n, nonzero, etc.}
have zero_lt_degree_X_sub_C : 0 < degree (X - C b),
  by { simp [degree_one_X_sub_C],
       sorry }, -- by const_polynomial???
have degree_X_add_C_lt_degree_f : degree (X - C b) < degree (map i f),
  by { rw ←degree_one_X_sub_C at hf,
       rw degree_map_eq_of_injective hi,
       assumption, },
exact @not_irreducible_of_degree_lt_div _ _ (map i f) (X - C b)
                                        zero_lt_degree_X_sub_C
                                        degree_X_add_C_lt_degree_f
                                        X_sub_C_dvd,
end


theorem splits_of_degree_two_root {f : polynomial α} {b : β}
    (hf : degree f = 2) (root : is_root (map i f) b) : splits i f :=
splits_of_degree_two_not_irreducible
  (not_irreducible_of_root hi
    (by { have hf' : 1 < degree f,
          by sorry,
          assumption }) root) hf
