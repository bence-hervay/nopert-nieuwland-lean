import Modules.Check.Number.Theta
import Modules.System.SystemOps
import Modules.System.PolyRootEq

/-!
# An exact root of a system over `ℤ[α]`

A point `x` written out exactly over a number field: `x i = aᵢ(α) / δ(α)` for elements `aᵢ`, `δ` of
`ℤ[α]` (`Check.ZTheta R`, `Modules/Check/Number/Theta.lean`), with `δ(α) > 0`. Every check is a
computation in `ℤ[α]` (`pointOk`):

* an equation `p = q`: for the common denominator `L` of its coefficients, `L (p - q)` has integer
  coefficients, and its terms homogenised to its largest degree `E` with `δ`,
  `∑ c (∏ aᵢ ^ eᵢ) δ ^ (E - deg)`, are zero in `ℤ[α]`; that element's value is
  `δ(α) ^ E L (p - q)(x)` (`hval_re`), so `p(x) = q(x)`;
* an interval `[a / b, a' / b']` of `x i`: `b aᵢ - a δ ≥ 0` and `a' δ - b' aᵢ ≥ 0`, decided on the
  enclosure of `α`.
* a polynomial `f` of `x 0` with integer coefficients: Horner's scheme homogenised with `δ`
  (`hornerQ`) gives `0`.

Then `x` is a root of the system (`solves_of_pointOk`). If the system has exactly one root and its
scale is `N` (`IsRootEq`), the point's first coordinate is `N` (`scale_eq_of_pointOk`), and a
polynomial `f` in one variable with `f(x 0) = 0` (`uniOk`) has `N` as a root
(`polyEval_eq_zero_of_uniOk`).

Nothing about the field is assumed: `α` is the root of `Root`'s kernel-checked data, and every
value is a definite real number.
-/

namespace Nieuwland.Check.ExactPoint

open Exact RationalPolynomial

variable {R : Root}

/-! ### Values in `ℤ[α]` -/

/-- `a ^ e`. -/
def pow (a : ZTheta R) : ℕ → ZTheta R
  | 0 => ofInt 1
  | e + 1 => pow a e * a

theorem re_pow (a : ZTheta R) : ∀ e, re (pow a e) = re a ^ e
  | 0 => by simp [pow, re_ofInt]
  | e + 1 => by rw [pow, re_mul, re_pow a e, pow_succ]

/-- The degree of the powers `m`. -/
def mdeg (m : List (ℕ × ℕ)) : ℕ := (m.map Prod.snd).sum

/-- The numerator of coordinate `i` (`0` beyond the list). -/
def coord (A : List (ZTheta R)) (i : ℕ) : ZTheta R := A.getD i (ofInt 0)

/-- `∏ aᵢ ^ eᵢ` over the powers `m`. -/
def mval (A : List (ZTheta R)) : List (ℕ × ℕ) → ZTheta R
  | [] => ofInt 1
  | v :: m => pow (coord A v.1) v.2 * mval A m

/-- The point: `x i = aᵢ(α) / δ(α)`. -/
noncomputable def pt (δ : ZTheta R) (A : List (ZTheta R)) (i : ℕ) : ℝ := re (coord A i) / re δ

theorem mval_re {δ : ZTheta R} (A : List (ZTheta R)) (hδ : re δ ≠ 0) :
    ∀ m, re (mval A m) = monomial (pt δ A) m * re δ ^ mdeg m
  | [] => by simp [mval, re_ofInt, monomial_nil, mdeg]
  | v :: m => by
    have ih := mval_re A hδ m
    have hc : re (coord A v.1) ^ v.2 = pt δ A v.1 ^ v.2 * re δ ^ v.2 := by
      rw [pt, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hδ)]
    simp only [mdeg] at ih ⊢
    rw [mval, re_mul, re_pow, ih, monomial_cons, List.map_cons, List.sum_cons, pow_add, hc]
    ring

/-! ### Integer polynomials, homogenised -/

/-- Integer terms `(c, m)`, each standing for `c ∏ x i ^ e`. -/
abbrev IntTerms := List (ℤ × List (ℕ × ℕ))

/-- The value of integer terms. -/
noncomputable def ieval (P : IntTerms) (x : ℕ → ℝ) : ℝ :=
  (P.map fun t ↦ (t.1 : ℝ) * monomial x t.2).sum

/-- The largest degree of the terms. -/
def maxDeg (P : IntTerms) : ℕ := P.foldr (fun t d ↦ max (mdeg t.2) d) 0

theorem le_maxDeg : ∀ (P : IntTerms), ∀ t ∈ P, mdeg t.2 ≤ maxDeg P
  | [], _, h => absurd h List.not_mem_nil
  | s :: P, t, h => by
    simp only [maxDeg, List.foldr_cons] at *
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (le_maxDeg P t h).trans (le_max_right _ _)

/-- `∑ c (∏ aᵢ ^ eᵢ) δ ^ (E - deg)`: `δ ^ E` times the terms at the point (`hval_re`). -/
def hval (δ : ZTheta R) (A : List (ZTheta R)) (E : ℕ) : IntTerms → ZTheta R
  | [] => ofInt 0
  | t :: P => ofInt t.1 * mval A t.2 * pow δ (E - mdeg t.2) + hval δ A E P

theorem hval_re {δ : ZTheta R} (A : List (ZTheta R)) (hδ : re δ ≠ 0) (E : ℕ) :
    ∀ P : IntTerms, (∀ t ∈ P, mdeg t.2 ≤ E) → re (hval δ A E P) = re δ ^ E * ieval P (pt δ A)
  | [], _ => by simp [hval, ieval, re_ofInt]
  | t :: P, h => by
    have ht := h t List.mem_cons_self
    have ih := hval_re A hδ E P fun s hs ↦ h s (List.mem_cons_of_mem _ hs)
    have hE : re δ ^ E = re δ ^ mdeg t.2 * re δ ^ (E - mdeg t.2) := by
      rw [← pow_add]; congr 1; omega
    rw [hval, re_add, re_mul, re_mul, re_ofInt, mval_re A hδ, re_pow, ih]
    simp only [ieval, List.map_cons, List.sum_cons]
    rw [hE]
    ring

/-! ### From rational coefficients -/

/-- The common denominator of the coefficients. -/
def denL (p : RationalPolynomial) : ℕ := p.foldr (fun t d ↦ Nat.lcm t.1.den d) 1

/-- Each coefficient times `L` is an integer. -/
def intOk (L : ℤ) (p : RationalPolynomial) : Bool :=
  p.all fun t : ℚ × List (ℕ × ℕ) ↦ (t.1 * (L : ℚ)).den == 1

/-- `L p` as integer terms. -/
def toInt (L : ℤ) (p : RationalPolynomial) : IntTerms :=
  p.map fun t : ℚ × List (ℕ × ℕ) ↦ ((t.1 * (L : ℚ)).num, t.2)

theorem ieval_toInt {L : ℤ} (x : ℕ → ℝ) :
    ∀ p : RationalPolynomial, intOk L p = true → ieval (toInt L p) x = L * p.eval x
  | [], _ => by simp [ieval, toInt]
  | t :: p, h => by
    simp only [intOk, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    have ih := ieval_toInt x p (by simpa [intOk] using h.2)
    have hc : (((t.1 * (L : ℚ)).num : ℤ) : ℝ) = (t.1 : ℝ) * L := by
      have := Rat.coe_int_num_of_den_eq_one h.1
      have h' : (((t.1 * (L : ℚ)).num : ℚ) : ℝ) = ((t.1 * (L : ℚ) : ℚ) : ℝ) := by rw [this]
      push_cast at h'
      exact h'
    simp only [toInt, List.map_cons, ieval, List.sum_cons] at ih ⊢
    rw [ih, hc, eval_cons]
    ring

theorem eval_append (p q : RationalPolynomial) (x : ℕ → ℝ) :
    (p ++ q).eval x = p.eval x + q.eval x := by
  simp [RationalPolynomial.eval, List.map_append, List.sum_append]

/-! ### Equations and intervals -/

/-- The equation `e.1 = e.2` holds at the point (`eqOk_sound`). -/
def eqOk (δ : ZTheta R) (A : List (ZTheta R)) (e : RationalPolynomial × RationalPolynomial) :
    Bool :=
  let d := e.1 ++ neg e.2
  let L : ℤ := denL d
  let P := toInt L d
  L != 0 && intOk L d && isZero (hval δ A (maxDeg P) P)

theorem eqOk_sound {δ : ZTheta R} {A : List (ZTheta R)} (hδ : re δ ≠ 0)
    {e : RationalPolynomial × RationalPolynomial} (h : eqOk δ A e = true) :
    e.1.eval (pt δ A) = e.2.eval (pt δ A) := by
  simp only [eqOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨hL, hi⟩, hz⟩ := h
  have h0 := isZero_sound _ hz
  rw [hval_re A hδ _ _ (le_maxDeg _), ieval_toInt _ _ hi, eval_append, eval_neg] at h0
  have hL' : ((denL (e.1 ++ neg e.2) : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hL
  have := (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ hδ)
  have := (mul_eq_zero.mp this).resolve_left hL'
  linarith

/-- `lo ≤ a(α) / δ(α) ≤ hi` for `δ(α) > 0` (`ivOk_sound`). -/
def ivOk (δ a : ZTheta R) (I : ℚ × ℚ) : Bool :=
  nonneg (ofInt I.1.den * a - ofInt I.1.num * δ) && nonneg (ofInt I.2.num * δ - ofInt I.2.den * a)

theorem ivOk_sound {δ a : ZTheta R} (hδ : 0 < re δ) {I : ℚ × ℚ} (h : ivOk δ a I = true) :
    (I.1 : ℝ) ≤ re a / re δ ∧ re a / re δ ≤ (I.2 : ℝ) := by
  simp only [ivOk, Bool.and_eq_true] at h
  have h1 := nonneg_sound _ h.1
  have h2 := nonneg_sound _ h.2
  simp only [re_sub, re_mul, re_ofInt] at h1 h2
  have hd1 : (0 : ℝ) < I.1.den := by exact_mod_cast I.1.pos
  have hd2 : (0 : ℝ) < I.2.den := by exact_mod_cast I.2.pos
  have e1 : (I.1 : ℝ) = I.1.num / I.1.den := Rat.cast_def I.1
  have e2 : (I.2 : ℝ) = I.2.num / I.2.den := Rat.cast_def I.2
  push_cast at h1 h2
  constructor
  · rw [e1, div_le_div_iff₀ hd1 hδ]
    linarith
  · rw [e2, div_le_div_iff₀ hδ hd2]
    linarith

/-! ### Roots -/

/-- **The check of an exact root**: `δ(α) > 0`, every interval of the box holds the point's
coordinate, and every equation holds there. -/
def pointOk (S : PolynomialSystem) (δ : ZTheta R) (A : List (ZTheta R)) : Bool :=
  pos δ && (List.range S.box.length).all (fun i ↦ ivOk δ (coord A i) (S.box.getD i (0, 0))) &&
    S.eqs.all (eqOk δ A)

theorem solves_of_pointOk {S : PolynomialSystem} {δ : ZTheta R} {A : List (ZTheta R)}
    (h : pointOk S δ A = true) : S.Solves (pt δ A) := by
  simp only [pointOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hp, hb⟩, he⟩ := h
  have hδ := pos_sound _ hp
  exact ⟨fun i hi ↦ ivOk_sound hδ (hb i hi), fun e he' ↦ eqOk_sound hδ.ne' (he e he')⟩

/-- **The point's scale**: if every system of `Ss` has exactly one root, at the scale `N`, and the
point solves one of them, its first coordinate is `N`. -/
theorem scale_eq_of_pointOk {Ss : List PolynomialSystem} {N : ℝ}
    (hN : PolynomialSystem.IsRootEq Ss N) {S : PolynomialSystem} (hS : S ∈ Ss) {δ : ZTheta R}
    {A : List (ZTheta R)} (h : pointOk S δ A = true) : pt δ A 0 = N := by
  have hs : pt δ A 0 ∈ PolynomialSystem.scales [S] :=
    ⟨S, List.mem_singleton_self _, _, solves_of_pointOk h, rfl⟩
  rw [(hN.2 S hS).2] at hs
  exact hs

theorem polyEval_cons (c : ℚ) (f : List ℚ) (x : ℝ) :
    polyEval (c :: f) x = c + x * polyEval f x := by
  simp only [polyEval, List.length_cons, Finset.sum_range_succ', List.getD_cons_succ,
    List.getD_cons_zero, pow_zero, mul_one, Finset.mul_sum]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- Horner's scheme, homogenised with `δ`: for `f` of length `n`, `∑ fᵢ xⁱ δ^(n-1-i)` and `δ ^ n`
(`hornerQ_re`); `2 n` products. Coefficients are read as integers (`uniOk` checks them). -/
def hornerQ (δ x : ZTheta R) : List ℚ → ZTheta R × ZTheta R
  | [] => (ofInt 0, ofInt 1)
  | c :: f => let r := hornerQ δ x f; (ofInt c.num * r.2 + x * r.1, r.2 * δ)

theorem hornerQ_snd (δ x : ZTheta R) : ∀ f : List ℚ, re (hornerQ δ x f).2 = re δ ^ f.length
  | [] => by simp [hornerQ, re_ofInt]
  | c :: f => by
    simp only [hornerQ]
    rw [re_mul, hornerQ_snd δ x f, List.length_cons, pow_succ]

theorem hornerQ_re {δ x : ZTheta R} (hδ : re δ ≠ 0) :
    ∀ f : List ℚ, f.all (fun c : ℚ ↦ c.den == 1) = true →
      re (hornerQ δ x f).1 * re δ = re δ ^ f.length * polyEval f (re x / re δ)
  | [], _ => by simp [hornerQ, re_ofInt, polyEval]
  | c :: f, h => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    have ih := hornerQ_re (x := x) hδ f h.2
    have hc : ((c.num : ℤ) : ℝ) = (c : ℝ) := by
      have := Rat.coe_int_num_of_den_eq_one h.1
      have h' : ((c.num : ℚ) : ℝ) = ((c : ℚ) : ℝ) := by rw [this]
      push_cast at h'
      exact h'
    simp only [hornerQ]
    rw [re_add, re_mul, re_mul, re_ofInt, hornerQ_snd, hc, polyEval_cons, List.length_cons]
    set y := re x / re δ with hy
    have hxy : re x = y * re δ := by rw [hy, div_mul_cancel₀ _ hδ]
    rw [hxy, pow_succ]
    linear_combination (y * re δ) * ih

/-- The polynomial `f` in one variable, with integer coefficients, vanishes at the point's first
coordinate (`uniOk_sound`): Horner's scheme homogenised with `δ` gives `0` in `ℤ[α]`. -/
def uniOk (δ : ZTheta R) (A : List (ZTheta R)) (f : List ℚ) : Bool :=
  pos δ && f.all (fun c : ℚ ↦ c.den == 1) && isZero (hornerQ δ (coord A 0) f).1

theorem uniOk_sound {δ : ZTheta R} {A : List (ZTheta R)} {f : List ℚ} (h : uniOk δ A f = true) :
    polyEval f (pt δ A 0) = 0 := by
  simp only [uniOk, Bool.and_eq_true] at h
  obtain ⟨⟨hp, hf⟩, hz⟩ := h
  have hδ := (pos_sound _ hp).ne'
  have := hornerQ_re (x := coord A 0) hδ f hf
  rw [isZero_sound _ hz, zero_mul] at this
  exact (mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero _ hδ)

/-- **A root of `f`**: if every system of `Ss` has exactly one root, at the scale `N`, and an exact
point solves one of them with `f(x 0) = 0`, then `f(N) = 0`. -/
theorem polyEval_eq_zero_of_uniOk {Ss : List PolynomialSystem} {N : ℝ}
    (hN : PolynomialSystem.IsRootEq Ss N) {S : PolynomialSystem} (hS : S ∈ Ss) {δ : ZTheta R}
    {A : List (ZTheta R)} (h : pointOk S δ A = true) {f : List ℚ} (hf : uniOk δ A f = true) :
    polyEval f N = 0 := by
  rw [← scale_eq_of_pointOk hN hS h]
  exact uniOk_sound hf

end Nieuwland.Check.ExactPoint
