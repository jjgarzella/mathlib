/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/

import field_theory.minimal_polynomial
import ring_theory.algebraic
import group_theory.congruence

/-!
# Ideals over/under ideals

This file concerns ideals lying over other ideals.
Let `f : R →+* S` be a ring homomorphism (typically a ring extension), `I` an ideal of `R` and
`J` an ideal of `S`. We say `J` lies over `I` (and `I` under `J`) if `I` is the `f`-preimage of `J`.
This is expressed here by writing `I = J.comap f`.
-/

variables {R : Type*} [comm_ring R]

namespace ideal

open polynomial
open submodule

section comm_ring
variables {S : Type*} [comm_ring S] {f : R →+* S} {I J : ideal S}

lemma coeff_zero_mem_comap_of_root_mem_of_eval_mem {r : S} (hr : r ∈ I) {p : polynomial R}
  (hp : p.eval₂ f r ∈ I) : p.coeff 0 ∈ I.comap f :=
begin
  rw [←p.div_X_mul_X_add, eval₂_add, eval₂_C, eval₂_mul, eval₂_X] at hp,
  refine mem_comap.mpr ((I.add_mem_iff_right _).mp hp),
  exact I.mul_mem_left hr
end

lemma coeff_zero_mem_comap_of_root_mem {r : S} (hr : r ∈ I) {p : polynomial R}
  (hp : p.eval₂ f r = 0) : p.coeff 0 ∈ I.comap f :=
coeff_zero_mem_comap_of_root_mem_of_eval_mem hr (hp.symm ▸ I.zero_mem)

lemma comap_eq_top_iff {I : ideal S} : I.comap f = ⊤ ↔ I = ⊤ :=
⟨ λ h, I.eq_top_iff_one.mpr (f.map_one ▸ mem_comap.mp ((I.comap f).eq_top_iff_one.mp h)),
  λ h, by rw [h, comap_top] ⟩

lemma hom_eq_zero_of_monic_of_map_eq_zero {p : polynomial R} (hp : p.monic) (hfp : p.map f = 0) :
  ∀ x, f x = 0 :=
λ x, calc f x = f x * f p.leading_coeff : by simp [hp]
     ... = f x * (p.map f).coeff p.nat_degree : by rw [polynomial.leading_coeff, ←coeff_map]
     ... = 0 : by simp [hfp]

lemma exists_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem {r : S}
  (r_non_zero_divisor : ∀ {x}, x * r = 0 → x = 0) (hr : r ∈ I)
  {p : polynomial R} : ∀ (p_ne_zero : p ≠ 0) (hp : p.eval₂ f r = 0),
  ∃ i, p.coeff i ≠ 0 ∧ p.coeff i ∈ I.comap f :=
begin
  refine p.rec_on_horner _ _ _,
  { intro h, contradiction },
  { intros p a coeff_eq_zero a_ne_zero ih p_ne_zero hp,
    refine ⟨0, _, coeff_zero_mem_comap_of_root_mem hr hp⟩,
    simp [coeff_eq_zero, a_ne_zero] },
  { intros p p_nonzero ih mul_nonzero hp,
    rw [eval₂_mul, eval₂_X] at hp,
    obtain ⟨i, hi, mem⟩ := ih p_nonzero (r_non_zero_divisor hp),
    refine ⟨i + 1, _, _⟩; simp [hi, mem] }
end

end comm_ring

section integral_domain
variables {S : Type*} [integral_domain S] {f : R →+* S} {I J : ideal S}

lemma exists_coeff_ne_zero_mem_comap_of_root_mem {r : S} (r_ne_zero : r ≠ 0) (hr : r ∈ I)
  {p : polynomial R} : ∀ (p_ne_zero : p ≠ 0) (hp : p.eval₂ f r = 0),
  ∃ i, p.coeff i ≠ 0 ∧ p.coeff i ∈ I.comap f :=
exists_coeff_ne_zero_mem_comap_of_non_zero_divisor_root_mem
  (λ _ h, or.resolve_right (mul_eq_zero.mp h) r_ne_zero) hr

@[simp] lemma lift_comp_mk (I : ideal R) (H : ∀ (a : R), a ∈ I → f a = 0) :
  (quotient.lift I f H).comp (quotient.mk I) = f :=
by { ext, exact @quotient.lift_mk _ _ _ _ _ I f H }

@[simp] lemma quotient.lift_comp {T : Type} [comm_ring T] (I : ideal R) (f : R →+* S) (g : S →+* T)
  (hf : ∀ (a : R), a ∈ I → f a = 0) (hgf : ∀ (a : R), a ∈ I → g (f a) = 0) :
  quotient.lift I (g.comp f) hgf = g.comp (quotient.lift I f hf) :=
ring_hom.ext (λ xbar, quot.induction_on xbar (λ x, by simp))

lemma quotient.mk_surjective (I : ideal R) : function.surjective (quotient.mk I) :=
begin
  rintro ⟨x⟩,
  exact ⟨x, rfl⟩
end

lemma mem_of_mem_quotient (hIJ : I ≤ J) {x : S}
  (mem : quotient.mk I x ∈ J.map (quotient.mk I)) : x ∈ J :=
begin
  obtain ⟨x, x_mem, x_eq⟩ := (set.mem_image _ _ _).mp
    (mem_image_of_mem_map_of_surjective (quotient.mk I) (quotient.mk_surjective I) mem),
  simpa using J.add_mem (hIJ (quotient.eq.mp x_eq.symm)) x_mem,
end

lemma exists_coeff_mem_comap_sdiff_comap_of_root_mem_sdiff
  [is_prime I] (hIJ : I ≤ J) {r : S} (hr : r ∈ (J : set S) \ I)
  {p : polynomial R} (p_ne_zero : p.map (quotient.mk (I.comap f)) ≠ 0) (hpI : p.eval₂ f r ∈ I) :
  ∃ i, p.coeff i ∈ (J.comap f : set R) \ (I.comap f) :=
begin
  obtain ⟨hrJ, hrI⟩ := hr,
  have rbar_ne_zero : quotient.mk I r ≠ 0 := mt (quotient.mk_eq_zero I).mp hrI,
  have rbar_mem_J : quotient.mk I r ∈ J.map (quotient.mk I) := mem_map_of_mem hrJ,
  have quotient_f : ∀ x ∈ I.comap f, (quotient.mk I).comp f x = 0,
  { simp [quotient.eq_zero_iff_mem] },
  have rbar_root : (p.map (quotient.mk (I.comap f))).eval₂
    (quotient.lift (I.comap f) _ quotient_f)
    (quotient.mk I r) = 0,
  { convert quotient.eq_zero_iff_mem.mpr hpI,
    exact trans (eval₂_map _ _ _) (hom_eval₂ p f (quotient.mk I) r).symm },
  obtain ⟨i, ne_zero, mem⟩ :=
    exists_coeff_ne_zero_mem_comap_of_root_mem rbar_ne_zero rbar_mem_J p_ne_zero rbar_root,
  rw coeff_map at ne_zero mem,
  refine ⟨i, mem_of_mem_quotient hIJ _, mt _ ne_zero⟩,
  { simpa using mem },
  simp [quotient.eq_zero_iff_mem],
end

lemma comap_ne_bot_of_root_mem {r : S} (r_ne_zero : r ≠ 0) (hr : r ∈ I)
  {p : polynomial R} (p_ne_zero : p ≠ 0) (hp : p.eval₂ f r = 0) :
  I.comap f ≠ ⊥ :=
λ h, let ⟨i, hi, mem⟩ := exists_coeff_ne_zero_mem_comap_of_root_mem r_ne_zero hr p_ne_zero hp in
absurd ((mem_bot _).mp (eq_bot_iff.mp h mem)) hi

lemma comap_lt_comap_of_root_mem_sdiff [I.is_prime] (hIJ : I ≤ J)
  {r : S} (hr : r ∈ (J : set S) \ I)
  {p : polynomial R} (p_ne_zero : p.map (quotient.mk (I.comap f)) ≠ 0) (hp : p.eval₂ f r ∈ I) :
  I.comap f < J.comap f :=
let ⟨i, hJ, hI⟩ := exists_coeff_mem_comap_sdiff_comap_of_root_mem_sdiff hIJ hr p_ne_zero hp
in lt_iff_le_and_exists.mpr ⟨comap_mono hIJ, p.coeff i, hJ, hI⟩

variables [algebra R S]

lemma comap_ne_bot_of_algebraic_mem {x : S}
  (x_ne_zero : x ≠ 0) (x_mem : x ∈ I) (hx : is_algebraic R x) : I.comap (algebra_map R S) ≠ ⊥ :=
let ⟨p, p_ne_zero, hp⟩ := hx
in comap_ne_bot_of_root_mem x_ne_zero x_mem p_ne_zero hp

lemma comap_ne_bot_of_integral_mem [nontrivial R] {x : S}
  (x_ne_zero : x ≠ 0) (x_mem : x ∈ I) (hx : is_integral R x) : I.comap (algebra_map R S) ≠ ⊥ :=
comap_ne_bot_of_algebraic_mem x_ne_zero x_mem (hx.is_algebraic R)

lemma mem_of_one_mem (h : (1 : S) ∈ I) (x) : x ∈ I :=
(I.eq_top_iff_one.mpr h).symm ▸ mem_top

lemma comap_lt_comap_of_integral_mem_sdiff [I.is_prime] (hIJ : I ≤ J)
  {x : S} (mem : x ∈ (J : set S) \ I) (integral : is_integral R x) :
  I.comap (algebra_map R S) < J.comap (algebra_map _ _) :=
begin
  obtain ⟨p, p_monic, hpx⟩ := integral,
  refine comap_lt_comap_of_root_mem_sdiff hIJ mem _ _,
  swap,
  { intro h,
    refine mem.2 (mem_of_one_mem _ _),
    rw [←(algebra_map R S).map_one, ←mem_comap, ←quotient.eq_zero_iff_mem],
    apply hom_eq_zero_of_monic_of_map_eq_zero p_monic h 1 },
  convert I.zero_mem
end

lemma is_maximal_of_is_integral_of_is_maximal_comap [nontrivial R]
  (hRS : ∀ (x : S), is_integral R x) (I : ideal S) [I.is_prime]
  (hI : is_maximal (I.comap (algebra_map R S))) : is_maximal I :=
⟨ mt comap_eq_top_iff.mpr hI.1,
  λ J I_lt_J, let ⟨I_le_J, x, hxJ, hxI⟩ := lt_iff_le_and_exists.mp I_lt_J
  in comap_eq_top_iff.mp (hI.2 _ (comap_lt_comap_of_integral_mem_sdiff I_le_J ⟨hxJ, hxI⟩ (hRS x))) ⟩

lemma integral_closure.comap_ne_bot [nontrivial R] {I : ideal (integral_closure R S)}
  (I_ne_bot : I ≠ ⊥) : I.comap (algebra_map R (integral_closure R S)) ≠ ⊥ :=
let ⟨x, x_mem, x_ne_zero⟩ := I.ne_bot_iff.mp I_ne_bot in
comap_ne_bot_of_integral_mem x_ne_zero x_mem (integral_closure.is_integral x)

lemma integral_closure.eq_bot_of_comap_eq_bot [nontrivial R] {I : ideal (integral_closure R S)} :
  I.comap (algebra_map R (integral_closure R S)) = ⊥ → I = ⊥ :=
imp_of_not_imp_not _ _ integral_closure.comap_ne_bot

lemma integral_closure.comap_lt_comap {I J : ideal (integral_closure R S)} [I.is_prime]
  (I_lt_J : I < J) :
  I.comap (algebra_map R (integral_closure R S)) < J.comap (algebra_map _ _) :=
let ⟨I_le_J, x, hxJ, hxI⟩ := lt_iff_le_and_exists.mp I_lt_J in
comap_lt_comap_of_integral_mem_sdiff I_le_J ⟨hxJ, hxI⟩ (integral_closure.is_integral x)

lemma integral_closure.is_maximal_of_is_maximal_comap [nontrivial R]
  (I : ideal (integral_closure R S)) [I.is_prime]
  (hI : is_maximal (I.comap (algebra_map R (integral_closure R S)))) : is_maximal I :=
is_maximal_of_is_integral_of_is_maximal_comap (λ x, integral_closure.is_integral x) I hI

end integral_domain

end ideal
