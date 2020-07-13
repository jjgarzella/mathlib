/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad
-/
import data.pfunctor.multivariate.W
universe u

/-!
# Multivariate quotients of polynomial functors.

Basic definition of multivariant QPF

## Related modules

 * constructions
   * fix
   * cofix
   * quot
   * comp

each proves that some operations on functors preserves the QPF structure

##reference

 * [Jeremy Avigad, Mario M. Carneiro and Simon Hudon, *Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]

-/

/--
Multivariate quotients of polynomial functors.
-/
class mvqpf {n : ℕ} (F : typevec.{u} n → Type*) [mvfunctor F] :=
(P         : mvpfunctor.{u} n)
(abs       : Π {α}, P.obj α → F α)
(repr      : Π {α}, F α → P.obj α)
(abs_repr  : ∀ {α} (x : F α), abs (repr x) = x)
(abs_map   : ∀ {α β} (f : α ⟹ β) (p : P.obj α), abs (f <$$> p) = f <$$> abs p)

namespace mvqpf
variables {n : ℕ} {F : typevec.{u} n → Type*} [mvfunctor F] [q : mvqpf F]
include q
open mvfunctor (liftp liftr)

/-
Show that every mvqpf is a lawful mvfunctor.
-/

protected theorem id_map {α : typevec n} (x : F α) : typevec.id <$$> x = x :=
by { rw ←abs_repr x, cases repr x with a f, rw [←abs_map], reflexivity }

@[simp] theorem comp_map {α β γ : typevec n} (f : α ⟹ β) (g : β ⟹ γ) (x : F α) :
  (g ⊚ f) <$$> x = g <$$> f <$$> x :=
by { rw ←abs_repr x, cases repr x with a f, rw [←abs_map, ←abs_map, ←abs_map], reflexivity }

@[priority 100]
instance is_lawful_mvfunctor : is_lawful_mvfunctor F :=
{ id_map := @mvqpf.id_map n F _ _,
  comp_map := @comp_map n F _ _ }

/- Lifting predicates and relations -/

theorem liftp_iff {α : typevec n} (p : Π ⦃i⦄, α i → Prop) (x : F α) :
  liftp p x ↔ ∃ a f, x = abs ⟨a, f⟩ ∧ ∀ i j, p (f i j) :=
begin
  split,
  { rintros ⟨y, hy⟩, cases h : repr y with a f,
    use [a, λ i j, (f i j).val], split,
    { rw [←hy, ←abs_repr y, h, ←abs_map], reflexivity },
    intros i j, apply (f i j).property },
  rintros ⟨a, f, h₀, h₁⟩, dsimp at *,
  use abs (⟨a, λ i j, ⟨f i j, h₁ i j⟩⟩),
  rw [←abs_map, h₀], reflexivity
end

theorem liftr_iff {α : typevec n} (r : Π ⦃i⦄, α i → α i → Prop) (x y : F α) :
  liftr r x y ↔ ∃ a f₀ f₁, x = abs ⟨a, f₀⟩ ∧ y = abs ⟨a, f₁⟩ ∧ ∀ i j, r (f₀ i j) (f₁ i j) :=
begin
  split,
  { rintros ⟨u, xeq, yeq⟩, cases h : repr u with a f,
    use [a, λ i j, (f i j).val.fst, λ i j, (f i j).val.snd],
    split, { rw [←xeq, ←abs_repr u, h, ←abs_map], refl },
    split, { rw [←yeq, ←abs_repr u, h, ←abs_map], refl },
    intros i j, exact (f i j).property },
  rintros ⟨a, f₀, f₁, xeq, yeq, h⟩,
  use abs ⟨a, λ i j, ⟨(f₀ i j, f₁ i j), h i j⟩⟩,
  dsimp, split,
  { rw [xeq, ←abs_map], refl },
  rw [yeq, ←abs_map], refl
end

open set
open mvfunctor

theorem mem_supp {α : typevec n} (x : F α) (i) (u : α i) :
  u ∈ supp x i ↔ ∀ a f, abs ⟨a, f⟩ = x → u ∈ f i '' univ :=
begin
  rw [supp], dsimp, split,
  { intros h a f haf,
    have : liftp (λ i u, u ∈ f i '' univ) x,
    { rw liftp_iff, refine ⟨a, f, haf.symm, _⟩,
      intros i u, exact mem_image_of_mem _ (mem_univ _) },
    exact h this },
  intros h p, rw liftp_iff,
  rintros ⟨a, f, xeq, h'⟩,
  rcases h a f xeq.symm with ⟨i, _, hi⟩,
  rw ←hi, apply h'
end

theorem supp_eq {α : typevec n} {i} (x : F α) : supp x i = { u | ∀ a f, abs ⟨a, f⟩ = x → u ∈ f i '' univ } :=
by ext; apply mem_supp

theorem has_good_supp_iff {α : typevec n} (x : F α) :
  (∀ p, liftp p x ↔ ∀ i (u ∈ supp x i), p i u) ↔
    ∃ a f, abs ⟨a, f⟩ = x ∧ ∀ i a' f', abs ⟨a', f'⟩ = x → f i '' univ ⊆ f' i '' univ :=
begin
  split,
  { intros h,
    have : liftp (supp x) x, by rw h, intro u, exact id,
    rw liftp_iff at this, rcases this with ⟨a, f, xeq, h'⟩,
    refine ⟨a, f, xeq.symm, _⟩,
    intros a' f' h'',
    rintros u ⟨j, _, hfi⟩,
    have hh : u ∈ supp x i, by rw ←hfi; apply h',
    refine (mem_supp x _ u).mp hh _ _ h'', },
  rintros ⟨a, f, xeq, h⟩ p, rw liftp_iff, split,
  { rintros ⟨a', f', xeq', h'⟩ u usuppx,
    rcases (mem_supp x _ u).mp @usuppx a' f' xeq'.symm with ⟨i, _, f'ieq⟩,
    rw ←f'ieq, apply h' },
  intro h',
  refine ⟨a, f, xeq.symm, _⟩, intros j y,
  apply h', rw mem_supp,
  intros a' f' xeq',
  apply h a' f' xeq',
  apply mem_image_of_mem _ (mem_univ _)
end

variable (q)

/-- A qpf is said to be uniform if every polynomial functor
representing a single value all have the same range. -/
def is_uniform : Prop := ∀ ⦃α : typevec n⦄ (a a' : q.P.A)
    (f : q.P.B a ⟹ α) (f' : q.P.B a' ⟹ α),
  abs ⟨a, f⟩ = abs ⟨a', f'⟩ → ∀ i, f i '' univ = f' i '' univ

variable [q]

theorem supp_eq_of_is_uniform (h : q.is_uniform) {α : typevec n} (a : q.P.A) (f : q.P.B a ⟹ α) :
  ∀ i, supp (abs ⟨a, f⟩) i = f i '' univ :=
begin
  intro, ext u, rw [mem_supp], split,
  { intro h', apply h' _ _ rfl },
  intros h' a' f' e,
  rw [←h _ _ _ _ e.symm], apply h'
end

theorem liftp_iff_of_is_uniform (h : q.is_uniform) {α : Type u} (x : F α) (p : α → Prop) :
  liftp p x ↔ ∀ u ∈ supp x, p u :=
begin
  rw [liftp_iff, ←abs_repr x],
  cases repr x with a f,  split,
  { rintros ⟨a', f', abseq, hf⟩ u,
    rw [supp_eq_of_is_uniform h, h _ _ _ _ abseq],
    rintros ⟨i, _, hi⟩, rw ←hi, apply hf },
  intro h',
  refine ⟨a, f, rfl, λ i, h' _ _⟩,
  rw supp_eq_of_is_uniform h,
  exact ⟨i, mem_univ i, rfl⟩
end

theorem supp_map (h : q.is_uniform) {α β : Type u} (g : α → β) (x : F α) :
  supp (g <$> x) = g '' supp x :=
begin
  rw ←abs_repr x, cases repr x with a f, rw [←abs_map, pfunctor.map_eq],
  rw [supp_eq_of_is_uniform h, supp_eq_of_is_uniform h, image_comp]
end

end mvqpf
