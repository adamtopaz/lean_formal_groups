import tactic
import ring_theory.power_series.basic

noncomputable theory
open_locale classical

variables {α β γ R : Type*} [comm_ring R]

example : α → α ⊕ β := sum.inl
example : β → α ⊕ β := sum.inr

example (f : α → γ) (g : β → γ) : α ⊕ β → γ := 
  λ t, sum.rec_on t f g

example (f : α → γ) (g : β → γ) : α ⊕ β → γ := λ t,
match t with
| sum.inl a := f a
| sum.inr b := g b
end

#check @dif_neg
#check @dif_pos
#check tactic.split_ifs

variables (α β R)

def incl_fun : mv_power_series α R → mv_power_series (α ⊕ β) R := 
  show ((α →₀ ℕ) → R) → ((α ⊕ β →₀ ℕ) → R), from λ f m, 
  let n := finsupp.sum_finsupp_equiv_prod_finsupp m in
  if n.2 = 0 then f n.1 else 0

def incl : mv_power_series α R →+* mv_power_series (α ⊕ β) R :=
{ to_fun := incl_fun α β R,
  map_one' := sorry,
  map_mul' := sorry,
  map_zero' := sorry,
  map_add' := sorry }

def incr_fun : mv_power_series β R → mv_power_series (α ⊕ β) R := 
  show ((β →₀ ℕ) → R) → ((α ⊕ β →₀ ℕ) → R), from λ f m, 
  let n := finsupp.sum_finsupp_equiv_prod_finsupp m in
  if n.1 = 0 then f n.2 else 0

def incr : mv_power_series β R →+* mv_power_series (α ⊕ β) R :=
{ to_fun := incr_fun α β R,
  map_one' := sorry,
  map_mul' := sorry,
  map_zero' := sorry,
  map_add' := sorry }