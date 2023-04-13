import tactic
import ring_theory.ideal.quotient
import ring_theory.power_series.basic
import ring_theory.polynomial.basic

noncomputable theory
open_locale classical
open_locale big_operators


variables (σ τ ω R : Type*) [comm_ring R]

namespace mv_power_series

#check finsupp.map_domain

variables {σ τ}

--set_option trace.simplify.rewrite true

@[simp]
lemma incl_monomial_aux (ι : σ ↪ τ) (m : σ →₀ ℕ) (t : σ) : 
  m.map_domain ι (ι t) = m t := 
begin
  dsimp [finsupp.map_domain],
  rw finsupp.sum_apply,
  have : m.sum (λ a n, ite (a = t) n 0) = m t,
  { simp only [finsupp.sum_ite_self_eq'] },
  convert this,
  ext a b,
  rw finsupp.single_apply,
  rw (ι.injective.eq_iff : ι a = ι t ↔ a = t) 
end

def incl_monomial (ι : σ ↪ τ) : (σ →₀ ℕ) ↪ (τ →₀ ℕ) := 
{ to_fun := λ m, finsupp.map_domain ι m,
  inj' := begin
    intros m1 m2 h,
    dsimp at h,
    ext t,
    apply_fun (λ e, e (ι t)) at h,
    simpa only [incl_monomial_aux] using h,
  end }

lemma incl_mon_add (ι : σ ↪ τ) (m : σ →₀ ℕ) (n : σ →₀ ℕ) : 
  incl_monomial ι (m + n) = incl_monomial ι m + incl_monomial ι n :=
  begin
    dsimp [incl_monomial],
    exact finsupp.map_domain_add,
  end

--R is being recognized as a variable here?
--Or variables {σ τ} changes them to be implicit instead of explicit variables, but R is not changed?
--That would not explain ω
def incl_fun (ι : σ ↪ τ) : mv_power_series σ R → mv_power_series τ R := 
λ f m, if h : ∃ m' : σ →₀ ℕ, incl_monomial ι m' = m then f h.some else 0

lemma incl_fun_spec (ι : σ ↪ τ) (m : σ →₀ ℕ) (n : τ →₀ ℕ) (hm : incl_monomial ι m = n) (f) :
  coeff R n (incl_fun R ι f) = coeff R m f :=
begin
  dsimp [incl_fun, coeff],
  split_ifs,
  { congr' 1,
    apply (incl_monomial ι).injective,
    rw [h.some_spec, hm] },
  { push_neg at h, 
    exfalso,
    apply h,
    exact hm }
end

@[simp]
lemma constant_coeff_incl (ι : σ ↪ τ) (f : mv_power_series σ R) : 
  constant_coeff τ R (incl_fun R ι f) = constant_coeff σ R f := 
begin
  apply incl_fun_spec,
  refl,
end

#check @Exists.some
#check @Exists.some_spec

lemma incl_one (ι : σ ↪ τ) : 
  incl_fun R ι 1 = 1 :=
begin
  ext m,
  simp only [mv_power_series.coeff_one],
  split_ifs,
  { simp [h] },
  { dsimp [incl_fun, coeff], split_ifs with hh hh,
    { let m' := hh.some, 
      have hm' : incl_monomial ι m' = m := hh.some_spec,
      have h' : m' ≠ 0, {
        contrapose! h,
        rw ← hm',
        rw h,
        refl,
      },
      change (coeff R m') 1 = 0,
      rw mv_power_series.coeff_one,
      rw if_neg h' },
    { refl } }
end

lemma incl_zero (ι : σ ↪ τ) :
  incl_fun R ι 0 = 0 :=
  begin
    ext m,
    simp only [mv_power_series.coeff_zero],
    dsimp [incl_fun, coeff],
    split_ifs;
    try {refl,},
  end

lemma incl_add (ι : σ ↪ τ) (F : mv_power_series σ R) (G : mv_power_series σ R) :
  incl_fun R ι (F + G) = incl_fun R ι F + incl_fun R ι G :=
  begin
    ext m,
    dsimp [incl_fun, coeff],
    split_ifs;
    simp,
  end

/-
lemma helper (ι : σ ↪ τ) (n : τ →₀ ℕ) (h : ¬∃ (m' : σ →₀ ℕ), incl_monomial ι m' = n)
  (p : (τ →₀ ℕ) × (τ →₀ ℕ)) (hh : p ∈ n.antidiagonal) :
  (¬∃ (m' : σ →₀ ℕ), incl_monomial ι m' = p.fst) ∨ (¬∃ (m' : σ →₀ ℕ), incl_monomial ι m' = p.snd) :=
  begin
    -- messy proof should try and clean up
    rw finsupp.mem_antidiagonal at hh,
    by_contra,
    rw ← and_iff_not_or_not at h,
    cases h with hl hr,
    let ml := hl.some,
    have hml := hl.some_spec,
    let mr := hr.some,
    have hmr := hr.some_spec,
    -- rw ← [hml, hmr] at hh, this does not work, how to fix?
    rw ← hml at hh,
    rw ← hmr at hh,
    rw ← incl_mon_add at hh,
    apply h,
    use (ml + mr),
    apply hh,
  end
-/

lemma incl_mul_h (ι : σ ↪ τ) (n : τ →₀ ℕ) (h : ¬∃ (m' : σ →₀ ℕ), incl_monomial ι m' = n) --need better name
  (F : mv_power_series σ R) (G : mv_power_series σ R) (p : (τ →₀ ℕ) × (τ →₀ ℕ)) (hh : p ∈ n.antidiagonal) :
  dite (∃ (m' : σ →₀ ℕ), incl_monomial ι m' = p.fst)
  (λ (h : ∃ (m' : σ →₀ ℕ), incl_monomial ι m' = p.fst), F h.some) 
  (λ (h : ¬∃ (m' : σ →₀ ℕ), incl_monomial ι m' = p.fst), 0) * 
  dite (∃ (m' : σ →₀ ℕ), incl_monomial ι m' = p.snd) 
  (λ (h : ∃ (m' : σ →₀ ℕ), incl_monomial ι m' = p.snd), G h.some) 
  (λ (h : ¬∃ (m' : σ →₀ ℕ), incl_monomial ι m' = p.snd), 0) = 0  :=
  begin
    split_ifs, {
      exfalso,
      apply h,
      use h_1.some + h_2.some,
      rw incl_mon_add,
      rw [h_1.some_spec, h_2.some_spec],
      rw finsupp.mem_antidiagonal at hh,
      exact hh,
    }, {
      ring,
    }, {
      ring,
    }, {
      ring,
    }
  end

def S (ι : σ ↪ τ) (n : τ →₀ ℕ) : finset ((τ →₀ ℕ) × (τ →₀ ℕ)) := 
  set.to_finset {p : (τ →₀ ℕ) × (τ →₀ ℕ) | p ∈ n.antidiagonal ∧
  (∃ (m' : σ →₀ ℕ), incl_monomial ι m' = p.fst) ∧ (∃ (m' : σ →₀ ℕ), incl_monomial ι m' = p.snd)}


lemma helper (ι : σ ↪ τ) (n : τ →₀ ℕ) (h : ∃ (m' : σ →₀ ℕ), incl_monomial ι m' = n)
  (F : mv_power_series σ R) (G : mv_power_series σ R) : 
  (∀ p : (τ →₀ ℕ) × (τ →₀ ℕ), p ∈ (n.antidiagonal \ S ι n) → 
  dite (∃ (m' : σ →₀ ℕ), incl_monomial ι m' = p.fst) 
  (λ (h : ∃ (m' : σ →₀ ℕ), incl_monomial ι m' = p.fst), F h.some) 
  (λ (h : ¬∃ (m' : σ →₀ ℕ), incl_monomial ι m' = p.fst), 0) * 
  dite (∃ (m' : σ →₀ ℕ), incl_monomial ι m' = p.snd) 
  (λ (h : ∃ (m' : σ →₀ ℕ), incl_monomial ι m' = p.snd), G h.some) 
  (λ (h : ¬∃ (m' : σ →₀ ℕ), incl_monomial ι m' = p.snd), 0) = 0) :=
  begin
    intros p hh,
    split_ifs, {
      exfalso,
      unfold S at hh,
      simp at hh,           --bad simp call
      cases hh with hhl hhr,
      have hh := hhr hhl,
      specialize hh h_1.some,
      have hh := hh h_1.some_spec,
      specialize hh h_2.some,
      exact hh h_2.some_spec,
    }, {
      ring,
    }, {
      ring,
    }, {
      ring,
    }
  end 
/-
lemma helper (ι : σ ↪ τ) (n : τ →₀ ℕ) (h : ∃ (m' : σ →₀ ℕ), incl_monomial ι m' = n)
  (F : mv_power_series σ R) (G : mv_power_series σ R) : 
  ∀ p : (τ →₀ ℕ) × (τ →₀ ℕ), p ∈ (n.antidiagonal \ S ι n) → func R ι F G p = 0 :=
  begin
  intros p hh,
  unfold func,
  split_ifs, {
      sorry,
    }, {
      ring,
    }, {
      ring,
    }, {
      ring,
    }
  end
-/

  /-dite (∃ (m' : σ →₀ ℕ), ⇑(incl_monomial ι) m' = p.fst) 
  (λ (h : ∃ (m' : σ →₀ ℕ), ⇑(incl_monomial ι) m' = p.fst), F h.some) 
  (λ (h : ¬∃ (m' : σ →₀ ℕ), ⇑(incl_monomial ι) m' = p.fst), 0) * 
  dite (∃ (m' : σ →₀ ℕ), ⇑(incl_monomial ι) m' = p.snd) 
  (λ (h : ∃ (m' : σ →₀ ℕ), ⇑(incl_monomial ι) m' = p.snd), G h.some) 
  (λ (h : ¬∃ (m' : σ →₀ ℕ), ⇑(incl_monomial ι) m' = p.snd), 0))-/

--(i : Π (a : α), a ∈ s → γ) (hi : ∀ (a : α) (ha : a ∈ s), i a ha ∈ t)

def sum_terms (ι : σ ↪ τ) (F : mv_power_series σ R) (G : mv_power_series σ R) :
  (τ →₀ ℕ) × (τ →₀ ℕ) → R :=
  λ p : (τ →₀ ℕ) × (τ →₀ ℕ), 
    dite (∃ (m' : σ →₀ ℕ), incl_monomial ι m' = p.fst) 
    (λ (h : ∃ (m' : σ →₀ ℕ), incl_monomial ι m' = p.fst), F h.some) 
    (λ (h : ¬∃ (m' : σ →₀ ℕ), incl_monomial ι m' = p.fst), 0) * 
    dite (∃ (m' : σ →₀ ℕ), incl_monomial ι m' = p.snd) 
    (λ (h : ∃ (m' : σ →₀ ℕ), incl_monomial ι m' = p.snd), G h.some) 
    (λ (h : ¬∃ (m' : σ →₀ ℕ), incl_monomial ι m' = p.snd), 0)

def bij_map (ι : σ ↪ τ) (n : τ →₀ ℕ) (h : ∃ (m' : σ →₀ ℕ), incl_monomial ι m' = n) : 
  Π (a : (σ →₀ ℕ) × (σ →₀ ℕ)), a ∈ h.some.antidiagonal → (τ →₀ ℕ) × (τ →₀ ℕ) := 
  begin
  intros a ha,
  split,
  exact incl_monomial ι a.1,
  exact incl_monomial ι a.2,
  end
-- should probably change this (idk if this is considered bad code)

lemma bij_map_into (ι : σ ↪ τ) (n : τ →₀ ℕ) (h : ∃ (m' : σ →₀ ℕ), incl_monomial ι m' = n ) : 
  ∀ (a : (σ →₀ ℕ) × (σ →₀ ℕ)) (ha : a ∈ h.some.antidiagonal), bij_map ι n h a ha ∈ S ι n :=
  begin
    intros a ha,
    dsimp [bij_map, S],
    simp,         --bad simp
    simp at ha,   --bad simp
    rw ← incl_mon_add,
    rw ha,
    exact h.some_spec,
  end

lemma bij_map_eq (ι : σ ↪ τ) (n : τ →₀ ℕ) (h : ∃ (m' : σ →₀ ℕ), incl_monomial ι m' = n )
  (F : mv_power_series σ R) (G : mv_power_series σ R) : 
  ∀ (a : (σ →₀ ℕ) × (σ →₀ ℕ)) (ha : a ∈ h.some.antidiagonal), 
  coeff R a.fst F * coeff R a.snd G = (sum_terms R ι F G) (bij_map ι n h a ha) :=
  begin
    intros a ha,
    dsimp [sum_terms, bij_map],
    have hh : (incl_monomial ι a.fst + incl_monomial ι a.snd = n), {
      simp at ha, --fix this later
      rw ← incl_mon_add,
      rw ha,
      exact h.some_spec,
    },
    split_ifs, {
      have hf : (h_1.some = a.fst), {
        apply (incl_monomial ι).injective,
        exact h_1.some_spec,
      }, 
      have hs : (h_2.some = a.snd), {
        apply (incl_monomial ι).injective,
        exact h_2.some_spec,
      },
      rw [hf, hs],
      refl,
    }, {
      exfalso,
      apply h_2,
      use a.snd,
    }, {
      exfalso,
      apply h_1,
      use a.fst,
    }, {
      exfalso,
      apply h_1,
      use a.fst,
    }
  end


lemma bij_map_inj (ι : σ ↪ τ) (n : τ →₀ ℕ) (h : ∃ (m' : σ →₀ ℕ), incl_monomial ι m' = n ) :
  ∀ (a b : (σ →₀ ℕ) × (σ →₀ ℕ)) (ha : a ∈ h.some.antidiagonal) (hb : b ∈ h.some.antidiagonal), 
  bij_map ι n h a ha = bij_map ι n h b hb → a = b :=
  begin
    intros a b ha hb hh,
    dsimp [bij_map] at hh,
    simp at hh, -- FIX
    cases hh,
    exact prod.ext hh_left hh_right,
  end

lemma bij_map_surj (ι : σ ↪ τ) (n : τ →₀ ℕ) (h : ∃ (m' : σ →₀ ℕ), incl_monomial ι m' = n ) :
  ∀ (b : (τ →₀ ℕ) × (τ →₀ ℕ)), b ∈ S ι n → (∃ (a : (σ →₀ ℕ) × (σ →₀ ℕ))
  (ha : a ∈ h.some.antidiagonal), b = bij_map ι n h a ha) :=
  begin
    intros b hb,
    dsimp [bij_map, S] at *,
    simp at hb, --AGAIN
    cases hb with hn hb,
    cases hb with hbl hbr,
    use (hbl.some, hbr.some),
    split, {
      simp, --And again
      apply (incl_monomial ι).injective,
      rw [incl_mon_add, hbl.some_spec, hbr.some_spec, h.some_spec],
      exact hn,
    }, {
      apply prod.ext, {
        simp,
        rw hbl.some_spec,
      }, {
        simp,
        rw hbr.some_spec,
      }
    }
  end



lemma incl_mul (ι : σ ↪ τ) (F : mv_power_series σ R) (G : mv_power_series σ R) :
  incl_fun R ι (F * G) = incl_fun R ι F * incl_fun R ι G := 
  begin
    ext n,
    rw [coeff_mul],
    dsimp [coeff, incl_fun],
    split_ifs, {  
      dsimp [mv_power_series.has_mul],
      have hh : (S ι n ⊆ n.antidiagonal), {
        intros p hh,
        unfold S at hh,
        simp at hh, --what was the thing to use?
        cases hh,
        simp,     --non-terminal simp
        exact hh_left,
      },
      rw ← finset.sum_subset_zero_on_sdiff hh (helper R ι n h F G) _, {
        rw finset.sum_bij (bij_map ι n h) (bij_map_into ι n h) (bij_map_eq R ι n h F G) (bij_map_inj ι n h), {
          exact bij_map_surj ι n h,
        },
      }, {
        intros x hx,
        refl,
      },
    }, {
      symmetry,
      apply finset.sum_eq_zero,
      intros p hh,
      exact incl_mul_h R ι n h F G p hh,
    }

  end

def incl (ι : σ ↪ τ) : mv_power_series σ R →+* mv_power_series τ R := 
{ to_fun := incl_fun _ ι,
  map_one' := incl_one _ _,
  map_mul' := incl_mul _ _,
  map_zero' := incl_zero _ _,
  map_add' := incl_add _ _, }

variable (σ)
def variable_ideal : ideal (mv_power_series σ R) :=
ideal.span (set.range mv_power_series.X)

noncomputable def degree_geq : ℕ → ideal (mv_power_series σ R) 
| 0 := ⊤
| (n+1) := degree_geq n * variable_ideal σ R

variables {σ τ ω R}
def congruent_mod (n : ℕ) (F G : mv_power_series σ R) : Prop :=
F - G ∈ degree_geq σ R n


open finset

variables {σ τ ω R}
def nth_pow (n : ℕ) (F : mv_power_series σ R) : mv_power_series σ R := (∏ i in range n, F)

--as this all stands it is almost complete, however I need to "add one to functions n"
/-
def add_one (n : τ →₀ ℕ) : τ →₀ ℕ :=
  λ (t : τ), ite (n t = 0) 0 (n t + 1)
-/
def comp_eval (G : σ → mv_power_series τ R) (n : τ →₀ ℕ) : σ → mv_polynomial τ R :=
  λ (s : σ), mv_power_series.trunc_fun n (G s)


def F_poly (F : mv_power_series σ R) (hF : finite σ ) (n : τ →₀ ℕ ) : mv_polynomial σ R :=
  mv_power_series.trunc_fun (finsupp.equiv_fun_on_finite.inv_fun (λ s : σ, ∑ t in n.support, n t)) F



def compose 
  (F : mv_power_series σ R) -- F(X_1,X_2,...,X_n) 
  (G : σ → mv_power_series τ R) -- G_1(X_1,...,X_m), ..., G_n(X_1,...,X_m)
  (hF : finite σ )
  (hG : ∀ i, congruent_mod 1 (G i) 0) :
  mv_power_series τ R := 
  λ (n : τ →₀ ℕ ), mv_polynomial.coeff n (mv_polynomial.eval₂ mv_polynomial.C (comp_eval G n) (F_poly F hF n))
  --(n : (τ →₀ ℕ) => ) -- F(G_1(X_1,...,X_m),...,G_n(X_1,...,X_m))
  --give auxillary m = 2* n (bit of a hack)


/-

def incl_fun : mv_power_series σ R → mv_power_series (σ ⊕ τ) R := 
  show ((σ →₀ ℕ) → R) → ((σ ⊕ τ →₀ ℕ) → R), from λ f m, 
  let n := finsupp.sum_finsupp_equiv_prod_finsupp m in
  if n.2 = 0 then f n.1 else 0

#check mv_polynomial.eval₂_hom 
-- mv_polynomial.C or.inl
/--begin
  ext m,
  unfold incl_fun,
  rw coeff_one,
  split_ifs,
  end,-/
def incl : mv_power_series σ R →+* mv_power_series (σ ⊕ τ) R :=
{ to_fun := incl_fun,
  map_one' :=  begin
  ext n,
  unfold incl_fun,
  rw coeff_one,
  simp,
  split_ifs,
  end,
  map_mul' := begin
  intros F G,
  ext,
  unfold incl_fun,
  simp,
  rw coeff_mul,
  end,
  map_zero' := begin
  ext,
  unfold incl_fun,
  simp,
  refl,
  end,
  map_add' := sorry }

def incr_fun : mv_power_series τ R → mv_power_series (σ ⊕ τ) R := 
  show ((τ →₀ ℕ) → R) → ((σ ⊕ τ →₀ ℕ) → R), from λ f m, 
  let n := finsupp.sum_finsupp_equiv_prod_finsupp m in
  if n.1 = 0 then f n.2 else 0

def incr : mv_power_series τ R →+* mv_power_series (σ ⊕ τ) R :=
{ to_fun := incr_fun,
  map_one' := sorry,
  map_mul' := sorry,
  map_zero' := sorry,
  map_add' := sorry }


def change_var (e : σ ≃ τ) : mv_power_series σ R ≃+* mv_power_series τ R := 
sorry

def compose 
  (F : mv_power_series σ R) -- F(X_1,X_2,...,X_n) 
  (G : σ → mv_power_series τ R) -- G_1(X_1,...,X_m), ..., G_n(X_1,...,X_m)
  (hG : ∀ i, congruent_mod 1 (G i) 0) :
  mv_power_series τ R := λ (n : τ →₀ ℕ ), --(n : (τ →₀ ℕ) => ) -- F(G_1(X_1,...,X_m),...,G_n(X_1,...,X_m))

sorry 

-/




end mv_power_series

#check function.embedding.inr

/-

structure mv_formal_group_law :=
(F : σ → mv_power_series (σ ⊕ σ) R)
(hF : finite σ)
(F_mod_2 : ∀ i, mv_power_series.congruent_mod 2 (F i) 
  (mv_power_series.X (sum.inl i) + mv_power_series.X (sum.inr i)))
(F_assoc : ∀ i, 
  mv_power_series.compose (F i) (sum.elim (mv_power_series.incl R function.embedding.inl ∘ F) 
  (mv_power_series.incl R function.embedding.inr ∘ mv_power_series.X)) _ _ -- should follow from F_mod_2
  = 
  mv_power_series.compose (F_i) (sum.elim (mv_power_series.incl R 
  (function.embedding.trans function.embedding.inl  function.embedding.inl) ∘ 
  mv_power_series.X) (mv_power_series.incl R (sum.elim 
  (function.embedding.trans function.embedding.inr  function.embedding.inl) function.embedding.inr)))) 
  -/
