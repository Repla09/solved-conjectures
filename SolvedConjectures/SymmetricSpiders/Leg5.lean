import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.IntervalCases

/-!
# Zero-rotatability of the regular spider with legs of length five

Number the center 0 and number the vertex at depth `d` of leg `i` by
`5*i + d` (legs start at 0, depths at 1). Each positive vertex indexes
its incoming edge. Labels are integers so all difference calculations
use ordinary integer subtraction.
-/
namespace SpiderL5

open Set

def parent (x : ℤ) : ℤ := if (x - 1) % 5 = 0 then 0 else x - 1

def weight (f : ℤ → ℤ) (x : ℤ) : ℤ := |f x - f (parent x)|

def Graceful (k : ℤ) (f : ℤ → ℤ) : Prop :=
  BijOn f (Icc 0 (5*k)) (Icc 0 (5*k)) ∧
  BijOn (weight f) (Icc 1 (5*k)) (Icc 1 (5*k))

private theorem bijOn_interval {a b : ℤ} {f : ℤ → ℤ}
    (hm : MapsTo f (Icc a b) (Icc a b)) (hi : InjOn f (Icc a b)) :
    BijOn f (Icc a b) (Icc a b) := by
  refine ⟨hm, hi, ?_⟩
  have h := @Finset.surjOn_of_injOn_of_card_le ℤ ℤ (Finset.Icc a b) (Finset.Icc a b) f
  simpa only [Finset.coe_Icc] using
    h (by simpa only [Finset.coe_Icc] using hm)
      (by simpa only [Finset.coe_Icc] using hi) le_rfl

/-- Rooted formula, evaluated at a leg and a zero-based position on it. -/
private def row (k i r : ℤ) : ℤ :=
  if r = 0 then 5*(k-i) else if r = 1 then 5*i+1 else if r = 2 then 5*(k-i)-1
  else if r = 3 then 5*i+2 else 5*(k-i)-2

def rooted (k x : ℤ) : ℤ :=
  if x = 0 then 0 else row k ((x-1)/5) ((x-1)%5)

private theorem row_bounds {k i r : ℤ} (hi : 0 ≤ i) (hik : i < k) :
    1 ≤ row k i r ∧ row k i r ≤ 5*k := by
  unfold row
  split_ifs <;> omega

private theorem row_inj {k i j r s : ℤ} (hr : 0 ≤ r) (hr' : r < 5) (hs : 0 ≤ s)
    (hs' : s < 5) (h : row k i r = row k j s) : i = j ∧ r = s := by
  unfold row at h
  split_ifs at h <;> omega

private theorem rooted_weight {k x : ℤ} (hx : 0 < x) (hx' : x ≤ 5*k) :
    weight (rooted k) x =
      if (x-1)%5 = 0 then 5*(k-(x-1)/5)
      else |5*(k-2*((x-1)/5)) - ((x-1)%5)| := by
  have hr : 0 ≤ (x-1)%5 := Int.emod_nonneg _ (by decide)
  have hr' : (x-1)%5 < 5 := Int.emod_lt_of_pos _ (by decide)
  unfold weight parent rooted row
  by_cases h : (x-1)%5 = 0
  · simp [h, show x ≠ 0 by omega, abs_of_nonneg (show 0 ≤ 5*(k-(x-1)/5) by omega)]
  · have hp : x-1 ≠ 0 := by omega
    have hd : (x-1-1)/5 = (x-1)/5 := by omega
    have hm : (x-1-1)%5 = (x-1)%5 - 1 := by omega
    simp only [h, ite_false, show x ≠ 0 by omega, hp, hd, hm]
    rcases (show (x-1)%5 = 1 ∨ (x-1)%5 = 2 ∨ (x-1)%5 = 3 ∨ (x-1)%5 = 4 by omega) with h₁|h₁|h₁|h₁
    all_goals (simp [h₁, abs_eq_abs]; omega)

theorem rooted_graceful {k : ℤ} (hk : 0 ≤ k) : Graceful k (rooted k) := by
  constructor
  · apply bijOn_interval
    · intro x hx
      obtain ⟨hlo, hhi⟩ := hx
      by_cases h : x = 0
      · simp [h, rooted, mem_Icc]; omega
      · have hb := row_bounds (k := k) (i := (x-1)/5) (r := (x-1)%5)
            (by omega) (by omega)
        simp only [rooted, h, ite_false, mem_Icc]; omega
    · intro x hx y hy he
      obtain ⟨hxl, hxh⟩ := hx
      obtain ⟨hyl, hyh⟩ := hy
      by_cases ex : x = 0 <;> by_cases ey : y = 0
      · omega
      · have hb := row_bounds (k := k) (i := (y-1)/5) (r := (y-1)%5)
            (by omega) (by omega)
        simp [rooted, ex, ey] at he; omega
      · have hb := row_bounds (k := k) (i := (x-1)/5) (r := (x-1)%5)
            (by omega) (by omega)
        simp [rooted, ex, ey] at he; omega
      · simp only [rooted, ex, ey, ite_false] at he
        obtain ⟨_, _⟩ := row_inj (by omega) (by omega) (by omega) (by omega) he
        omega
  · apply bijOn_interval
    · intro x hx
      obtain ⟨hxl, hxh⟩ := hx
      rw [rooted_weight (by omega) hxh, mem_Icc]
      simp only [abs_eq_max_neg]
      split_ifs <;> omega
    · intro x hx y hy he
      obtain ⟨hxl, hxh⟩ := hx
      obtain ⟨hyl, hyh⟩ := hy
      rw [rooted_weight (by omega) hxh, rooted_weight (by omega) hyh] at he
      simp only [abs_eq_max_neg] at he
      split_ifs at he <;> omega


/-- Every edge of the seed crosses the cut after the center's label. -/
private def Crosses (s : ℤ) (f : ℤ → ℤ) : Prop :=
  ∀ x ∈ Icc 1 (5*s), (f x ≤ f 0 ↔ f (parent x) > f 0)

private def stretch (m c y : ℤ) := if y ≤ c then y else y+m

private def insert (s n : ℤ) (f : ℤ → ℤ) (x : ℤ) : ℤ :=
  if x ≤ 5*s then stretch (5*n) (f 0) (f x) else f 0 + rooted n (x-5*s)

private theorem insert_weight {s n : ℤ} {f : ℤ → ℤ} (hs : 0 ≤ s) (hn : 0 ≤ n)
    (hc : Crosses s f) {x : ℤ} (hx : 1 ≤ x) :
    weight (insert s n f) x =
      if x ≤ 5*s then weight f x + 5*n else weight (rooted n) (x-5*s) := by
  by_cases h : x ≤ 5*s
  · have hp : parent x ≤ 5*s := by unfold parent; split <;> omega
    have cut := hc x ⟨hx, h⟩
    simp only [weight, insert, h, hp, ite_true, stretch, abs_eq_max_neg]
    split_ifs <;> omega
  · have hm : (x-5*s-1)%5 = (x-1)%5 := by omega
    by_cases z : (x-1)%5 = 0
    · simp [weight, insert, parent, h, hm, z, show 0 ≤ 5*s by omega, stretch, rooted]
    · have hp : ¬ x-1 ≤ 5*s := by omega
      have eq : x-5*s-1 = x-1-5*s := by omega
      simp [weight, insert, parent, z, h, hp, eq]

private theorem rooted_positive {n x : ℤ} (hx : 0 < x) (hh : x ≤ 5*n) :
    1 ≤ rooted n x ∧ rooted n x ≤ 5*n := by
  simpa [rooted, show x ≠ 0 by omega] using
    (row_bounds (k := n) (i := (x-1)/5) (r := (x-1)%5) (by omega) (by omega))

private theorem insert_graceful {s n : ℤ} {f : ℤ → ℤ}
    (hs : 0 ≤ s) (hn : 0 ≤ n) (hf : Graceful s f) (hc : Crosses s f) :
    Graceful (s+n) (insert s n f) := by
  obtain ⟨hv, hw⟩ := hf
  obtain ⟨rv, rwts⟩ := rooted_graceful hn
  obtain ⟨cl, ch⟩ := hv.mapsTo (x := 0) ⟨le_rfl, by omega⟩
  constructor
  · apply bijOn_interval
    · intro x ⟨hx, hh⟩
      by_cases h : x ≤ 5*s
      · obtain ⟨l, u⟩ := hv.mapsTo (x := x) ⟨hx, h⟩
        simp only [insert, h, ite_true, stretch, mem_Icc]; split_ifs <;> omega
      · have hb := rooted_positive (n := n) (x := x-5*s) (by omega) (by omega)
        simp only [insert, h, ite_false, mem_Icc]; omega
    · intro x ⟨xl, xh⟩ y ⟨yl, yh⟩ he
      by_cases ex : x ≤ 5*s <;> by_cases ey : y ≤ 5*s
      · apply hv.injOn ⟨xl, ex⟩ ⟨yl, ey⟩
        simp only [insert, ex, ey, ite_true, stretch] at he
        split_ifs at he <;> omega
      · have hb := rooted_positive (n := n) (x := y-5*s) (by omega) (by omega)
        simp only [insert, ex, ey, ite_true, ite_false, stretch] at he
        split_ifs at he <;> omega
      · have hb := rooted_positive (n := n) (x := x-5*s) (by omega) (by omega)
        simp only [insert, ex, ey, ite_true, ite_false, stretch] at he
        split_ifs at he <;> omega
      · simp only [insert, ex, ey, ite_false, add_right_inj] at he
        have eq := rv.injOn (x₁ := x-5*s) (x₂ := y-5*s)
          ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ he
        omega
  · apply bijOn_interval
    · intro x ⟨hx, hh⟩
      rw [insert_weight hs hn hc hx]
      by_cases h : x ≤ 5*s
      · obtain ⟨l, u⟩ := hw.mapsTo (x := x) ⟨hx, h⟩
        simp only [h, ite_true, mem_Icc]; omega
      · obtain ⟨l, u⟩ := rwts.mapsTo (x := x-5*s) ⟨by omega, by omega⟩
        simp only [h, ite_false, mem_Icc]; omega
    · intro x ⟨xl, xh⟩ y ⟨yl, yh⟩ he
      rw [insert_weight hs hn hc xl, insert_weight hs hn hc yl] at he
      by_cases ex : x ≤ 5*s <;> by_cases ey : y ≤ 5*s
      · apply hw.injOn ⟨xl, ex⟩ ⟨yl, ey⟩
        simpa only [ex, ey, ite_true, add_left_inj] using he
      · obtain ⟨l, u⟩ := hw.mapsTo (x := x) ⟨xl, ex⟩
        obtain ⟨l', u'⟩ := rwts.mapsTo (x := y-5*s) ⟨by omega, by omega⟩
        simp only [ex, ey, ite_true, ite_false] at he; omega
      · obtain ⟨l, u⟩ := hw.mapsTo (x := y) ⟨yl, ey⟩
        obtain ⟨l', u'⟩ := rwts.mapsTo (x := x-5*s) ⟨by omega, by omega⟩
        simp only [ex, ey, ite_true, ite_false] at he; omega
      · simp only [ex, ey, ite_false] at he
        have eq := rwts.injOn (x₁ := x-5*s) (x₂ := y-5*s)
          ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ he
        omega


private def middle (x : ℤ) : ℤ := ([4, 7, 0, 10, 1, 9, 5, 3, 8, 2, 6] : List ℤ)[x.toNat]?.getD 0
private def tip (x : ℤ) : ℤ := ([2, 3, 1, 4, 0, 5] : List ℤ)[x.toNat]?.getD 0
private def single (x : ℤ) : ℤ := ([1, 4, 0, 5, 3, 2] : List ℤ)[x.toNat]?.getD 0

/-- Reduce each claim about a fixed seed to its entries, in the kernel. -/
local macro "check_seed" : tactic => `(tactic|
  (constructor <;> apply bijOn_interval
   all_goals first
     | (intro x ⟨xl, xh⟩ y ⟨yl, yh⟩; interval_cases x <;> interval_cases y <;> decide)
     | (intro x ⟨xl, xh⟩; interval_cases x <;> decide)))

private theorem middle_ok : Graceful 2 middle := by check_seed
private theorem tip_ok : Graceful 1 tip := by check_seed
private theorem single_ok : Graceful 1 single := by check_seed

private theorem middle_cut : Crosses 2 middle := by
  intro x ⟨xl, xh⟩; interval_cases x <;> decide

private theorem tip_cut : Crosses 1 tip := by
  intro x ⟨xl, xh⟩; interval_cases x <;> decide

private theorem complement {k : ℤ} {f : ℤ → ℤ} (hf : Graceful k f) :
    Graceful k (fun x => 5*k - f x) := by
  have hc : BijOn (fun y => 5*k-y) (Icc 0 (5*k)) (Icc 0 (5*k)) := by
    apply bijOn_interval
    · intro x ⟨l,u⟩; change 0 ≤ 5*k-x ∧ 5*k-x ≤ 5*k; constructor <;> omega
    · intro x _ y _ he; dsimp at he; omega
  refine ⟨hc.comp hf.1, hf.2.congr ?_⟩
  intro x _
  simp only [weight, abs_eq_abs]; omega

/-- Representatives on the first leg, with the center indexed by depth zero. -/
theorem first_leg {k d : ℤ} (hk : 1 ≤ k) (hd : d ∈ Icc 0 5) :
    ∃ f, Graceful k f ∧ f d = 0 := by
  have hr := rooted_graceful (k := k) (by omega)
  have ht := insert_graceful (n := k-1) (by decide) (by omega) tip_ok tip_cut
  rw [show 1 + (k-1) = k by omega] at ht
  have pair : ∃ f, Graceful k f ∧ f 2 = 0 ∧ f 3 = 5*k := by
    by_cases h : k = 1
    · subst k; exact ⟨single, single_ok, by decide, by decide⟩
    · have hm := insert_graceful (n := k-2) (by decide) (by omega) middle_ok middle_cut
      rw [show 2 + (k-2) = k by omega] at hm
      refine ⟨_, hm, ?_, ?_⟩
      · rfl
      · change 10 + 5*(k-2) = 5*k; omega
  obtain ⟨dl, du⟩ := hd
  obtain ⟨g, hg, h₂, h₃⟩ := pair
  interval_cases d
  · exact ⟨_, hr, by simp [rooted]⟩
  · refine ⟨_, complement hr, ?_⟩
    change 5*k - 5*(k-0) = 0; omega
  · exact ⟨_, hg, h₂⟩
  · exact ⟨_, complement hg, by simp [h₃]⟩
  · exact ⟨_, ht, rfl⟩
  · refine ⟨_, complement ht, ?_⟩
    change 5*k - (5 + 5*(k-1)) = 0; omega


/-- Cyclically renumber the legs, making old leg `i` the first leg. -/
private def rotate (k i x : ℤ) : ℤ :=
  if x = 0 then 0 else if x ≤ 5*i then x+5*k-5*i else x-5*i

private theorem rotate_bij {k i a : ℤ} (hi : 0 ≤ i) (hik : i < k) (ha : a = 0 ∨ a = 1) :
    BijOn (rotate k i) (Icc a (5*k)) (Icc a (5*k)) := by
  apply bijOn_interval
  · intro x ⟨l,u⟩
    unfold rotate; rw [mem_Icc]; split_ifs <;> omega
  · intro x ⟨xl,xu⟩ y ⟨yl,yu⟩ he
    unfold rotate at he; split_ifs at he <;> omega

private theorem rotate_parent {k i x : ℤ} (hi : 0 ≤ i) (hik : i < k)
    (xl : 1 ≤ x) (xu : x ≤ 5*k) :
    rotate k i (parent x) = parent (rotate k i x) := by
  unfold parent rotate
  split_ifs <;> omega

/-- Every vertex of T(k,5) admits zero under some graceful labeling. -/
theorem zero_rotatable {k : ℕ} (hk : 1 ≤ k) (v : ℤ) (hv : v ∈ Icc 0 (5*(k : ℤ))) :
    ∃ f, Graceful k f ∧ f v = 0 := by
  obtain ⟨vl, vu⟩ := hv
  by_cases h : v = 0
  · subst v; exact first_leg (by omega) (by decide)
  let i := (v-1)/5
  have il : 0 ≤ i := by dsimp [i]; omega
  have iu : i < (k : ℤ) := by dsimp [i]; omega
  obtain ⟨f, hf, hz⟩ := first_leg (k := (k : ℤ)) (d := v-5*i) (by omega)
    ⟨by dsimp [i]; omega, by dsimp [i]; omega⟩
  refine ⟨f ∘ rotate k i, ⟨hf.1.comp (rotate_bij il iu (Or.inl rfl)), ?_⟩, ?_⟩
  · apply (hf.2.comp (rotate_bij il iu (Or.inr rfl))).congr
    intro x ⟨xl, xu⟩
    simp only [Function.comp_apply, weight, rotate_parent il iu xl xu]
  · simpa [Function.comp_apply, rotate, h, show ¬ v ≤ 5*i by dsimp [i]; omega] using hz

end SpiderL5
