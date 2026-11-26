import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Zero-rotatability of symmetric spiders

The local rank of a low path label is its distance from 0. The local rank
of a high label is its distance from the largest label. Thus an edge's
weight is the largest label minus the sum of its two ranks.
-/
namespace SpiderGeneral
open Set

def parent (L x : ℤ) : ℤ := if (x-1) % L = 0 then 0 else x-1

def weight (L : ℤ) (f : ℤ → ℤ) (x : ℤ) : ℤ := |f x - f (parent L x)|

def Graceful (L k : ℤ) (f : ℤ → ℤ) : Prop :=
  BijOn f (Icc 0 (L*k)) (Icc 0 (L*k)) ∧
  BijOn (weight L f) (Icc 1 (L*k)) (Icc 1 (L*k))

private theorem bijOn_interval {a b : ℤ} {f : ℤ → ℤ}
    (hm : MapsTo f (Icc a b) (Icc a b)) (hi : InjOn f (Icc a b)) :
    BijOn f (Icc a b) (Icc a b) := by
  refine ⟨hm, hi, ?_⟩
  have h := @Finset.surjOn_of_injOn_of_card_le ℤ ℤ (Finset.Icc a b) (Finset.Icc a b) f
  simpa only [Finset.coe_Icc] using
    h (by simpa only [Finset.coe_Icc] using hm)
      (by simpa only [Finset.coe_Icc] using hi) le_rfl

private def adj (p : ℤ → ℤ) (j : ℤ) := p j + p (j-1)

/-- Each parity class uses its own ranks exactly once. The consecutive
rank sums use the integers from 0 through n-2 exactly once. -/
private structure Ranks (n : ℤ) (p : ℤ → ℤ) : Prop where
  bound : ∀ j, 0 ≤ j → j < n → 0 ≤ p j ∧ 2*p j + j%2 < n
  inj : ∀ i j, 0 ≤ i → i < n → 0 ≤ j → j < n → i%2 = j%2 → p i = p j → i = j
  edge : ∀ j, 1 ≤ j → j < n → 0 ≤ adj p j ∧ adj p j < n-1
  unique : ∀ i j, 1 ≤ i → i < n → 1 ≤ j → j < n → adj p i = adj p j → i = j

private def walecki (j : ℤ) := j/2

private theorem walecki_ok (n : ℤ) : Ranks n walecki := by
  constructor <;> simp only [adj, walecki] <;> intros <;> omega

private def rev (n : ℤ) (p : ℤ → ℤ) (j : ℤ) := p (n-1-j)

private theorem rev_ok {n p} (h : Ranks n p) : Ranks n (rev n p) := by
  have e (j : ℤ) : adj (rev n p) j = adj p (n-j) := by
    simp only [adj, rev, show n-1-(j-1) = n-j by omega, show n-1-j = n-j-1 by omega, add_comm]
  constructor
  · intro j l u
    have := h.bound (n-1-j) (by omega) (by omega)
    unfold rev; omega
  · intro i j il iu jl ju par eq
    have := h.inj (n-1-i) (n-1-j) (by omega) (by omega) (by omega) (by omega) (by omega) eq
    omega
  · intro j l u
    rw [e]; exact h.edge _ (by omega) (by omega)
  · intro i j il iu jl ju eq
    rw [e,e] at eq
    have := h.unique _ _ (by omega) (by omega) (by omega) (by omega) eq
    omega

private def flip (n : ℤ) (p : ℤ → ℤ) (j : ℤ) := (n-1-j%2)/2 - p j

private theorem flip_ok {n p} (h : Ranks n p) : Ranks n (flip n p) := by
  have e (j : ℤ) : adj (flip n p) j = n-2-adj p j := by unfold adj flip; omega
  constructor
  · intro j l u; have := h.bound j l u; unfold flip; omega
  · intro i j il iu jl ju par eq
    apply h.inj i j il iu jl ju par
    unfold flip at eq; omega
  · intro j l u; have := h.edge j l u; rw [e]; omega
  · intro i j il iu jl ju eq
    apply h.unique i j il iu jl ju
    rwa [e,e,sub_right_inj] at eq

/-- Append a second path, shifting each rank by the number of positions of
its parity in the prefix. The two shifts sum to t, so the edge sums of the
suffix start at t. The joining edge must supply the missing sum t-1. -/
private def join (t : ℤ) (p q : ℤ → ℤ) (j : ℤ) :=
  if j < t then p j else q (j-t) + (t+1-j%2)/2

private theorem join_ok {t s p q} (ht : 0 < t) (hs : 0 < s)
    (hp : Ranks t p) (hq : Ranks s q) (seam : p (t-1) + q 0 = (t-1)/2) :
    Ranks (t+s) (join t p q) := by
  have edgeForm (j : ℤ) : adj (join t p q) j =
      if j < t then adj p j else if j = t then t-1 else adj q (j-t) + t := by
    unfold adj join
    split_ifs <;> first | rfl | omega | (subst_vars; simp only [sub_self] at *; omega) |
      (rw [show j-1-t = j-t-1 by omega]; omega)
  constructor
  · intro j l u
    by_cases a : j < t
    · have := hp.bound j l a; simp [join, a]; omega
    · have := hq.bound (j-t) (by omega) (by omega); simp [join, a]; omega
  · intro i j il iu jl ju par eq
    by_cases a : i < t <;> by_cases b : j < t
    · exact hp.inj i j il a jl b par (by simpa [join,a,b] using eq)
    · have := hp.bound i il a
      have := hq.bound (j-t) (by omega) (by omega); simp [join,a,b] at eq; omega
    · have := hp.bound j jl b
      have := hq.bound (i-t) (by omega) (by omega); simp [join,a,b] at eq; omega
    · simp only [join,a,b,ite_false,par,add_left_inj] at eq
      have := hq.inj _ _ (by omega) (by omega) (by omega) (by omega) (by omega) eq
      omega
  · intro j l u
    rw [edgeForm]; split_ifs with a b
    · have := hp.edge j l a; omega
    · omega
    · have := hq.edge (j-t) (by omega) (by omega); omega
  · intro i j il iu jl ju eq
    rw [edgeForm,edgeForm] at eq
    split_ifs at eq
    all_goals first
      | exact hp.unique _ _ il (by omega) jl (by omega) eq
      | (have := hq.unique (i-t) (j-t) (by omega) (by omega) (by omega) (by omega) (by omega)
         omega)
      | omega
      | (try have := hp.edge i il (by omega)
         try have := hp.edge j jl (by omega)
         try have := hq.edge (i-t) (by omega) (by omega)
         have := hq.edge (j-t) (by omega) (by omega)
         omega)

private def Allowed (n x : ℤ) : Prop := 0 ≤ x ∧ 2*x < n ∧ (x = 0 ∨ n ≠ 4*x+1)

/-- Reflect ranks to put the prescribed start y in the lower half of its
class. A reversed Walecki prefix of either length 2y+1 or 2y+2 starts at y
and ends at 0. Both lengths require the suffix to start at y, and at least
one gives an admissible shorter problem. -/
private theorem endpoint (n x : ℤ) (hx : Allowed n x) :
    ∃ p, Ranks n p ∧ p 0 = x := by
  have build (y : ℤ) (hy : Allowed n y) (small : y ≤ (n-1)/2-y) :
      ∃ p, Ranks n p ∧ p 0 = y := by
    by_cases zero : y = 0
    · exact ⟨walecki, walecki_ok n, by simpa [walecki] using zero.symm⟩
    obtain ⟨t, ht, tail⟩ : ∃ t, (t = 2*y+1 ∨ t = 2*y+2) ∧ Allowed (n-t) y := by
      unfold Allowed at *
      by_cases a : n-(2*y+1) = 4*y+1
      · exact ⟨_, Or.inr rfl, by omega⟩
      · exact ⟨_, Or.inl rfl, by omega⟩
    obtain ⟨q,hq,start⟩ := endpoint (n-t) y tail
    have pos : 0 < t := by unfold Allowed at hy; omega
    have pos' : 0 < n-t := by unfold Allowed at tail; omega
    have h := join_ok pos pos' (rev_ok (walecki_ok t)) hq (by simp [rev,walecki,start]; omega)
    rw [show t+(n-t) = n by omega] at h
    exact ⟨_, h, by simp [join, pos, rev, walecki]; omega⟩
  by_cases small : x ≤ (n-1)/2-x
  · exact build x hx small
  · obtain ⟨p,hp,e⟩ := build ((n-1)/2-x) (by unfold Allowed at *; omega) (by omega)
    exact ⟨_, flip_ok hp, by simp [flip,e]⟩
termination_by n.toNat
decreasing_by unfold Allowed at *; omega

private def entries (l : List ℤ) (j : ℤ) := l[j.toNat]?.getD 0

private def nine := entries [1,2,2,0,0,1,4,3,3]
private def thirteen := entries [2,5,6,4,5,3,0,0,1,1,3,2,4]

local macro "check_ranks" : tactic => `(tactic|
  (constructor
   · intro j l u; interval_cases j <;> decide
   · intro i j il iu jl ju; interval_cases i <;> interval_cases j <;> decide
   · intro j l u; interval_cases j <;> decide
   · intro i j il iu jl ju; interval_cases i <;> interval_cases j <;> decide))

private theorem nine_ok : Ranks 9 nine := by check_ranks
private theorem thirteen_ok : Ranks 13 thirteen := by check_ranks

/-- Put rank zero at a specified position in the nearer half of the path.
The last two ranks of a reversed Walecki prefix of length at least two are
both zero. Ending this prefix at d or d+1 gives two possible seams. -/
private theorem near_zero {n d : ℤ} (hn : 6 ≤ n) (hd : 0 ≤ d) (near : 2*d < n) :
    ∃ p, Ranks n p ∧ p d = 0 := by
  by_cases ordinary : ∃ t, (t = d+1 ∨ t = d+2) ∧ Allowed (n-t) ((t-1)/2)
  · obtain ⟨t,ht,ha⟩ := ordinary
    obtain ⟨q,hq,e⟩ := endpoint _ _ ha
    have pos : 0 < n-t := by unfold Allowed at ha; omega
    have h := join_ok (show 0 < t by omega) pos (rev_ok (walecki_ok t)) hq
      (by simp [rev,walecki,e])
    rw [show t+(n-t) = n by omega] at h
    exact ⟨_, h, by simp [join, show d < t by omega, rev,walecki]; omega⟩
  · have bad₁ : ¬ Allowed (n-(d+1)) ((d+1-1)/2) := fun h => ordinary ⟨_,Or.inl rfl,h⟩
    have bad₂ : ¬ Allowed (n-(d+2)) ((d+2-1)/2) := fun h => ordinary ⟨_,Or.inr rfl,h⟩
    unfold Allowed at bad₁ bad₂
    by_cases a : n = 9 ∧ d = 3
    · obtain ⟨rfl,rfl⟩ := a; exact ⟨nine,nine_ok,by decide⟩
    by_cases b : n = 13 ∧ d = 6
    · obtain ⟨rfl,rfl⟩ := b; exact ⟨thirteen,thirteen_ok,by decide⟩
    -- Here n = 4s+1 and d = 2s. Make a front path starting with 1,0,0.
    -- Reversing it puts 0 at depth d and 1 at its last position, so the
    -- required rank at the start of the suffix drops by one.
    let t := d+2
    have tpos : 3 < t := by dsimp [t]; omega
    obtain ⟨q,hq,eq⟩ := endpoint (t-3) 1 (by unfold Allowed; dsimp [t]; omega)
    let front := join 3 (rev 3 walecki) q
    have hfront : Ranks t front := by
      have h := join_ok (by decide : (0:ℤ)<3) (by omega : 0<t-3) (rev_ok (walecki_ok 3)) hq
        (by rw [eq]; decide)
      rwa [show 3+(t-3) = t by omega] at h
    obtain ⟨r,hr,er⟩ := endpoint (n-t) ((t-1)/2-1) (by unfold Allowed; dsimp [t]; omega)
    have h := join_ok (by omega : 0<t) (by dsimp [t]; omega : 0<n-t) (rev_ok hfront) hr
      (by simp [rev,front,join,walecki,er])
    rw [show t+(n-t) = n by omega] at h
    refine ⟨_,h,?_⟩
    have e : t-1-d = 1 := by dsimp [t]; omega
    simp [join, show d<t by dsimp [t]; omega, rev,e,front,walecki]

private theorem prescribed {n d : ℤ} (hn : 6 ≤ n) (hl : 0 ≤ d) (hu : d < n) :
    ∃ p, Ranks n p ∧ p d = 0 := by
  by_cases h : 2*d < n
  · exact near_zero hn hl h
  · obtain ⟨p,hp,e⟩ := near_zero (d := n-1-d) hn (by omega) (by omega)
    exact ⟨_,rev_ok hp,e⟩

private def label (n : ℤ) (p : ℤ → ℤ) (j : ℤ) :=
  if j%2 = 0 then p j else n-1-p j

private def diff (a : ℤ → ℤ) (j : ℤ) := |a j - a (j-1)|

private structure Path (n : ℤ) (a : ℤ → ℤ) : Prop where
  bound : ∀ j, 0 ≤ j → j < n → 0 ≤ a j ∧ a j < n
  inj : ∀ i j, 0 ≤ i → i < n → 0 ≤ j → j < n → a i = a j → i = j
  edge : ∀ j, 1 ≤ j → j < n → 1 ≤ diff a j ∧ diff a j < n
  unique : ∀ i j, 1 ≤ i → i < n → 1 ≤ j → j < n → diff a i = diff a j → i = j

private theorem rankDiff {n p} (hp : Ranks n p) {j} (jl : 1 ≤ j) (ju : j < n) :
    diff (label n p) j = n-1-adj p j := by
  have := hp.edge j jl ju
  unfold diff label; unfold adj at *
  simp only [abs_eq_max_neg]; split_ifs <;> omega

private theorem label_ok {n p} (hp : Ranks n p) : Path n (label n p) := by
  constructor
  · intro j l u; have := hp.bound j l u; unfold label; split_ifs <;> omega
  · intro i j il iu jl ju e
    have := hp.bound i il iu; have := hp.bound j jl ju
    apply hp.inj i j il iu jl ju <;> unfold label at e <;> split_ifs at e <;> omega
  · intro j l u; have := hp.edge j l u; rw [rankDiff hp l u]; omega
  · intro i j il iu jl ju e
    rw [rankDiff hp il iu,rankDiff hp jl ju] at e
    exact hp.unique i j il iu jl ju (by omega)

private theorem path_compl {n a} (h : Path n a) : Path n (fun j => n-1-a j) := by
  have e (j : ℤ) : diff (fun z => n-1-a z) j = diff a j := by
    simp only [diff, abs_eq_abs]; omega
  constructor
  · intro j l u; have := h.bound j l u; omega
  · intro i j il iu jl ju eq
    exact h.inj i j il iu jl ju (by omega)
  · intro j l u; rw [e]; exact h.edge j l u
  · intro i j il iu jl ju eq; rw [e,e] at eq; exact h.unique i j il iu jl ju eq

/-- The exceptional endpoint for alternating labels on 4x+1 vertices.
The outer block contributes weights 2x+1,...,4x, the join contributes
2x, and the inner block contributes weights 1,...,2x-1. -/
private def exceptional (x j : ℤ) :=
  if j ≤ 2*x then
    if j%2 = 0 then (2*x-j)/2 else 4*x-(2*x-j)/2
  else
    let b := j-(2*x+1)
    if b%2 = 0 then 2*x-b/2 else 2*x+1+b/2

private theorem exceptional_ok {x : ℤ} (hx : 0 < x) : Path (4*x+1) (exceptional x) := by
  have e (j : ℤ) (l : 1 ≤ j) (u : j < 4*x+1) : diff (exceptional x) j =
      if j ≤ 2*x then 2*x+j else if j = 2*x+1 then 2*x else j-(2*x+1) := by
    simp only [diff, exceptional, abs_eq_max_neg]; split_ifs <;> omega
  constructor
  · intro j l u; simp only [exceptional]; split_ifs <;> omega
  · intro i j il iu jl ju eq; simp only [exceptional] at eq; split_ifs at eq <;> omega
  · intro j l u; rw [e j l u]; split_ifs <;> omega
  · intro i j il iu jl ju eq; rw [e i il iu,e j jl ju] at eq; split_ifs at eq <;> omega

private theorem ordinary_path {n x : ℤ} (xl : 0 ≤ x) (xu : x < n) :
    ∃ a, Path n a ∧ a 0 = x := by
  have low (y : ℤ) (l : 0 ≤ y) (u : 2*y < n) : ∃ a, Path n a ∧ a 0 = y := by
    by_cases hy : Allowed n y
    · obtain ⟨p,h,e⟩ := endpoint n y hy
      exact ⟨_,label_ok h,by simp [label,e]⟩
    · unfold Allowed at hy
      have eq : n = 4*y+1 := by omega
      subst n
      exact ⟨_,exceptional_ok (x := y) (by omega), by simp [exceptional, show 0 ≤ 2*y by omega]⟩
  by_cases h : 2*x < n
  · exact low x xl h
  · obtain ⟨a,ha,e⟩ := low (n-1-x) (by omega) (by omega)
    exact ⟨_,path_compl ha,by simp [e]⟩

/-! ## Packing the additional legs into blocks of length L -/

private theorem block_bound {L n i r : ℤ} (hl : 0 < L) (il : 0 ≤ i) (iu : i < n)
    (rl : 1 ≤ r) (ru : r ≤ L) : L*i+r ∈ Icc 1 (L*n) := by
  have := mul_nonneg hl.le il
  have := mul_le_mul_of_nonneg_left (show i+1 ≤ n by omega) hl.le
  constructor <;> linarith

private theorem block_inj {L i j r s : ℤ} (hl : 0 < L) (rl : 1 ≤ r) (ru : r ≤ L)
    (sl : 1 ≤ s) (su : s ≤ L) (eq : L*i+r = L*j+s) : i = j ∧ r = s := by
  have sep (a b u v : ℤ) (ab : a < b) (hu : u ≤ L) (hv : 1 ≤ v) : L*a+u < L*b+v := by
    have := mul_le_mul_of_nonneg_left (show a+1 ≤ b by omega) hl.le
    linarith
  rcases lt_trichotomy i j with h|rfl|h
  · have := sep _ _ _ _ h ru sl; omega
  · exact ⟨rfl,by omega⟩
  · have := sep _ _ _ _ h su rl; omega

private theorem coords {L n y : ℤ} (hl : 0 < L) (h : y ∈ Icc 1 (L*n)) :
    ∃ i j, 0 ≤ i ∧ i < n ∧ 0 ≤ j ∧ j < L ∧ y = L*i+j+1 := by
  obtain ⟨yl,yu⟩ := h
  refine ⟨(y-1)/L,(y-1)%L,Int.ediv_nonneg (by omega) hl.le,?_,
    Int.emod_nonneg _ (by omega),Int.emod_lt_of_pos _ hl,?_⟩
  · apply Int.ediv_lt_of_lt_mul hl; rw [mul_comm]; omega
  · have := Int.emod_add_mul_ediv (y-1) L; omega

private def atRow (L : ℤ) (row : ℤ → ℤ → ℤ) (y : ℤ) :=
  row ((y-1)/L) ((y-1)%L)

private theorem at_row {L i j : ℤ} {row} (hl : 0 < L) (jl : 0 ≤ j) (ju : j < L) :
    atRow L row (L*i+j+1) = row i j := by
  simp [atRow, Int.mul_add_ediv_left _ _ (ne_of_gt hl), Int.ediv_eq_zero_of_lt jl ju,
    Int.emod_eq_of_lt jl ju]

private theorem rows_bij {L n : ℤ} {row : ℤ → ℤ → ℤ} (hl : 0 < L)
    (bounds : ∀ i j, 0 ≤ i → i < n → 0 ≤ j → j < L → row i j ∈ Icc 1 (L*n))
    (inj : ∀ i j u v, 0 ≤ i → i < n → 0 ≤ j → j < L → 0 ≤ u → u < n → 0 ≤ v → v < L →
      row i j = row u v → i = u ∧ j = v) :
    BijOn (atRow L row) (Icc 1 (L*n)) (Icc 1 (L*n)) := by
  apply bijOn_interval
  · intro x hx; obtain ⟨i,j,il,iu,jl,ju,rfl⟩ := coords hl hx
    rw [at_row hl jl ju]; exact bounds i j il iu jl ju
  · intro x hx y hy eq
    obtain ⟨i,j,il,iu,jl,ju,rfl⟩ := coords hl hx
    obtain ⟨u,v,ul,uu,vl,vu,rfl⟩ := coords hl hy
    rw [at_row hl jl ju,at_row hl vl vu] at eq
    obtain ⟨rfl,rfl⟩ := inj _ _ _ _ il iu jl ju ul uu vl vu eq
    rfl

private def block (n i j : ℤ) := if j%2 = 0 then n-1-i else i

private def row (L n : ℤ) (a : ℤ → ℤ) (i j : ℤ) := L*block n i j + (a j+1)

private theorem rows_vertices {L n a} (hl : 0 < L) (h : Path L a) :
    BijOn (atRow L (row L n a)) (Icc 1 (L*n)) (Icc 1 (L*n)) := by
  apply rows_bij hl
  · intro i j il iu jl ju
    have := h.bound j jl ju
    apply block_bound hl _ _ (by omega) (by omega) <;> unfold block <;> split_ifs <;> omega
  · intro i j u v il iu jl ju ul uu vl vu eq
    have := h.bound j jl ju; have := h.bound v vl vu
    obtain ⟨b,r⟩ := block_inj hl (r := a j+1) (s := a v+1) (by omega) (by omega)
      (by omega) (by omega) eq
    obtain rfl := h.inj _ _ jl ju vl vu (by omega)
    unfold block at b; split_ifs at b <;> exact ⟨by omega,rfl⟩

/-- For a fixed internal edge, orient the difference between the two path
labels positively. Reversing the order of the legs absorbs its sign. -/
private def oriented (a : ℤ → ℤ) (j : ℤ) :=
  if j%2 = 0 then a j-a (j-1) else a (j-1)-a j

private def coeff (n : ℤ) (a : ℤ → ℤ) (i j : ℤ) :=
  if 0 ≤ oriented a j then n-1-2*i else -(n-1-2*i)

private theorem row_diff {L n a i j} :
    |row L n a i j - row L n a i (j-1)| = |L*coeff n a i j + diff a j| := by
  have norm : diff a j = |oriented a j| := by
    simp only [diff,oriented,abs_eq_abs]; split_ifs <;> omega
  rw [norm]; unfold row block coeff
  by_cases e : j%2 = 0
  · simp only [e,show (j-1)%2 ≠ 0 by omega,ite_true,ite_false,oriented]
    split_ifs with sign
    · rw [abs_of_nonneg sign]; congr 1; ring
    · rw [abs_of_neg (by omega : a j - a (j-1) < 0),abs_eq_abs]; right; ring
  · simp only [e,show (j-1)%2 = 0 by omega,ite_true,ite_false,oriented]
    split_ifs with sign
    · rw [abs_of_nonneg sign,abs_eq_abs]; right; ring
    · rw [abs_of_neg (by omega : a (j-1) - a j < 0)]; congr 1; ring

private def edgeRow (L n : ℤ) (a : ℤ → ℤ) (i j : ℤ) :=
  if j = 0 then L*(n-i) else |row L n a i j - row L n a i (j-1)|

/-- Fold a signed coefficient into a nonnegative block number. Its parity
determines which branch was used; within a negative block the residue runs
backwards. Center edges occupy the last residue in each block. -/
private def edgeBlock (n : ℤ) (a : ℤ → ℤ) (i j : ℤ) :=
  if j = 0 then n-1-i else
    if 0 ≤ coeff n a i j then coeff n a i j else -coeff n a i j-1

private def residue (L n : ℤ) (a : ℤ → ℤ) (i j : ℤ) :=
  if j = 0 then L else if 0 ≤ coeff n a i j then diff a j else L-diff a j

private theorem edge_code {L n a i j} (hl : 0 < L) (h : Path L a) (jl : 0 ≤ j) (ju : j < L) :
    edgeRow L n a i j = L*edgeBlock n a i j + residue L n a i j := by
  unfold edgeRow edgeBlock residue
  split_ifs with z s
  · ring
  · have b := h.edge j (by omega) ju
    rw [row_diff,abs_of_nonneg (by have := mul_nonneg hl.le s; omega)]
  · have b := h.edge j (by omega) ju
    have := mul_le_mul_of_nonneg_left (show coeff n a i j ≤ -1 by omega) hl.le
    rw [row_diff,abs_of_neg (by linarith : L*coeff n a i j + diff a j < 0)]
    ring

private theorem rows_edges {L n a} (hl : 0 < L) (h : Path L a) :
    BijOn (atRow L (edgeRow L n a)) (Icc 1 (L*n)) (Icc 1 (L*n)) := by
  have rb (i j : ℤ) (jl : 0 ≤ j) (ju : j < L) :
      1 ≤ residue L n a i j ∧ residue L n a i j ≤ L ∧ (residue L n a i j = L ↔ j = 0) := by
    by_cases z : j = 0
    · simp [residue,z]; omega
    · have := h.edge j (by omega) ju; simp [residue,z]; split_ifs <;> omega
  apply rows_bij hl
  · intro i j il iu jl ju
    have b := rb i j jl ju
    rw [edge_code hl h jl ju]
    apply block_bound hl _ _ b.1 b.2.1 <;> unfold edgeBlock coeff <;> split_ifs <;> omega
  · intro i j u v il iu jl ju ul uu vl vu eq
    have b := rb i j jl ju; have c := rb u v vl vu
    rw [edge_code hl h jl ju,edge_code hl h vl vu] at eq
    obtain ⟨be,re⟩ := block_inj hl b.1 b.2.1 c.1 c.2.1 eq
    by_cases z : j = 0
    · have z' : v = 0 := by omega
      simp [edgeBlock,z,z'] at be; exact ⟨by omega,by omega⟩
    · have z' : v ≠ 0 := by omega
      have parity (w r : ℤ) : coeff n a w r % 2 = (n-1)%2 := by
        unfold coeff; split_ifs <;> omega
      have pj := parity i j; have pv := parity u v
      simp only [edgeBlock,residue,z,z',ite_false] at be re
      have signs : (0 ≤ coeff n a i j) ↔ (0 ≤ coeff n a u v) := by
        split_ifs at be <;> omega
      have same : diff a j = diff a v := by rw [if_congr signs rfl rfl] at re; split_ifs at re <;> omega
      obtain rfl := h.unique j v (by omega) ju (by omega) vu same
      have co : coeff n a i j = coeff n a u j := by split_ifs at be <;> omega
      unfold coeff at co; split_ifs at co <;> exact ⟨by omega,rfl⟩

/-! ## Insert the blocks between the low and high labels of the first leg -/

private def stretch (c m y : ℤ) := if y ≤ c then y else y+m

private def glue (L c m : ℤ) (head tail : ℤ → ℤ) (x : ℤ) :=
  if x ≤ L then stretch c m (head x) else c + tail (x-L)

/-- A bijection on the first interval and a bijection onto a gap of size m
combine to give a bijection on the whole interval. -/
private theorem glue_bij {L c m lo : ℤ} {head tail : ℤ → ℤ} (hm : 0 ≤ m)
    (cl : lo ≤ c+1) (cu : c ≤ L)
    (hh : BijOn head (Icc lo L) (Icc lo L)) (ht : BijOn tail (Icc 1 m) (Icc 1 m)) :
    BijOn (glue L c m head tail) (Icc lo (L+m)) (Icc lo (L+m)) := by
  apply bijOn_interval
  · intro x ⟨xl,xu⟩
    by_cases e : x ≤ L
    · obtain ⟨l,u⟩ := hh.mapsTo (x := x) ⟨xl,e⟩
      simp only [glue,e,ite_true,stretch,mem_Icc]; split_ifs <;> omega
    · obtain ⟨l,u⟩ := ht.mapsTo (x := x-L) ⟨by omega,by omega⟩
      simp only [glue,e,ite_false,mem_Icc]; omega
  · intro x ⟨xl,xu⟩ y ⟨yl,yu⟩ eq
    by_cases ex : x ≤ L <;> by_cases ey : y ≤ L
    · apply hh.injOn ⟨xl,ex⟩ ⟨yl,ey⟩
      simp only [glue,ex,ey,ite_true,stretch] at eq; split_ifs at eq <;> omega
    · obtain ⟨l,u⟩ := ht.mapsTo (x := y-L) ⟨by omega,by omega⟩
      simp only [glue,ex,ey,ite_true,ite_false,stretch] at eq; split_ifs at eq <;> omega
    · obtain ⟨l,u⟩ := ht.mapsTo (x := x-L) ⟨by omega,by omega⟩
      simp only [glue,ex,ey,ite_true,ite_false,stretch] at eq; split_ifs at eq <;> omega
    · simp only [glue,ex,ey,ite_false,add_right_inj] at eq
      have := ht.injOn (x₁ := x-L) (x₂ := y-L) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ eq
      omega

private theorem path_vertices {L a} (h : Path (L+1) a) : BijOn a (Icc 0 L) (Icc 0 L) := by
  apply bijOn_interval
  · intro j ⟨l,u⟩; have := h.bound j l (by omega); exact ⟨by omega,by omega⟩
  · intro i ⟨il,iu⟩ j ⟨jl,ju⟩ e; exact h.inj _ _ il (by omega) jl (by omega) e

private theorem path_edges {L a} (h : Path (L+1) a) :
    BijOn (diff a) (Icc 1 L) (Icc 1 L) := by
  apply bijOn_interval
  · intro j ⟨l,u⟩; have := h.edge j l (by omega); exact ⟨by omega,by omega⟩
  · intro i ⟨il,iu⟩ j ⟨jl,ju⟩ e; exact h.unique _ _ il (by omega) jl (by omega) e

/-- Stretch the first leg across a gap of L*n labels. On the additional
legs, even and odd positions of the auxiliary path use the blocks in
opposite orders. The start of that path makes the center-edge weights
exactly the positive multiples of L through L*n. -/
private def spider (L n : ℤ) (p a : ℤ → ℤ) :=
  glue L (L/2) (L*n) (label (L+1) p) (atRow L (row L n a))

private theorem spider_graceful {L n p a} (hl : 0 < L) (hn : 0 ≤ n) (hp : Ranks (L+1) p)
    (ha : Path L a) (start : a 0 = L-1+p 0-L/2) : Graceful L (n+1) (spider L n p a) := by
  have hm := mul_nonneg hl.le hn
  have seed := label_ok hp
  have low (j : ℤ) (jl : 0 ≤ j) (ju : j ≤ L) : label (L+1) p j ≤ L/2 ↔ j%2 = 0 := by
    have := hp.bound j jl (by omega); unfold label; split_ifs <;> omega
  have center : spider L n p a 0 = p 0 := by
    have l := (low 0 (by omega) hl.le).2 (by decide)
    simp only [spider,glue,hl.le,ite_true,stretch,l]
    simp [label]
  have additional (i j : ℤ) (il : 0 ≤ i) (jl : 0 ≤ j) (ju : j < L) :
      spider L n p a (L+(L*i+j+1)) = L/2 + row L n a i j := by
    have := mul_nonneg hl.le il
    simp only [spider,glue,show ¬ L+(L*i+j+1) ≤ L by omega,ite_false,add_sub_cancel_left]
    rw [at_row hl jl ju]
  unfold Graceful
  rw [show L*(n+1) = L+L*n by ring]
  constructor
  · exact glue_bij hm (by omega) (by omega) (path_vertices seed) (rows_vertices hl ha)
  · apply (glue_bij (c := 0) hm (by omega) hl.le (path_edges seed) (rows_edges hl ha)).congr
    intro x ⟨xl,xu⟩
    by_cases ex : x ≤ L
    · have par : parent L x = x-1 := by
        simp only [parent,Int.emod_eq_of_lt (show 0 ≤ x-1 by omega) (show x-1 < L by omega)]
        split_ifs <;> omega
      have b := seed.edge x xl (by omega)
      have sides := low x (by omega) ex
      have sides' := low (x-1) (by omega) (by omega)
      simp only [weight,par,spider,glue,ex,show x-1 ≤ L by omega,ite_true,stretch,
        show ¬ diff (label (L+1) p) x ≤ 0 by omega,ite_false]
      unfold diff; simp only [abs_eq_max_neg]; split_ifs <;> omega
    · obtain ⟨i,j,il,iu,jl,ju,coord⟩ := coords hl (show x-L ∈ Icc 1 (L*n) from ⟨by omega,by omega⟩)
      have xx : x = L+(L*i+j+1) := by omega
      have par : parent L x = if j = 0 then 0 else L+(L*i+(j-1)+1) := by
        have eq : x-1 = L*(i+1)+j := by rw [xx]; ring
        simp only [parent,eq,Int.mul_add_emod_self_left,Int.emod_eq_of_lt jl ju]
        split_ifs <;> ring
      simp only [glue,ex,ite_false,zero_add,coord,at_row hl jl ju,weight,par]
      rw [xx,additional i j il jl ju]
      by_cases z : j = 0
      · subst j
        simp only [ite_true,center,edgeRow,row,block,Int.zero_emod,start]
        have nn := mul_nonneg hl.le (show 0 ≤ n-i by omega)
        rw [abs_of_nonneg (by linarith)]; ring
      · simp only [z,ite_false,edgeRow,additional i (j-1) il (by omega) (by omega),add_sub_add_left_eq_sub]

private theorem complement {L k f} (hf : Graceful L k f) :
    Graceful L k (fun x => L*k-f x) := by
  have h : BijOn (fun y => L*k-y) (Icc 0 (L*k)) (Icc 0 (L*k)) := by
    apply bijOn_interval
    · intro x ⟨l,u⟩; change 0 ≤ L*k-x ∧ L*k-x ≤ L*k; omega
    · intro x _ y _ e; change L*k-x = L*k-y at e; omega
  refine ⟨h.comp hf.1,hf.2.congr ?_⟩
  intro x _; simp only [weight,abs_eq_abs]; omega

private theorem first_leg {L n d : ℤ} (hl : 5 ≤ L) (hn : 0 ≤ n) (hd : d ∈ Icc 0 L) :
    ∃ f, Graceful L (n+1) f ∧ f d = 0 := by
  obtain ⟨dl,du⟩ := hd
  obtain ⟨p,hp,e⟩ := prescribed (n := L+1) (d := d) (by omega) dl (by omega)
  have c := hp.bound 0 (by omega) (by omega)
  obtain ⟨a,ha,start⟩ := ordinary_path (n := L) (x := L-1+p 0-L/2) (by omega) (by omega)
  have hf := spider_graceful (by omega : 0 < L) hn hp ha start
  by_cases even : d%2 = 0
  · exact ⟨_,hf,by simp [spider,glue,du,stretch,label,even,e,show 0 ≤ L/2 by omega]⟩
  · refine ⟨_,complement hf,?_⟩
    simp only [spider,glue,du,ite_true,label,even,ite_false,e,sub_zero,add_sub_cancel_right,
      stretch,show ¬ L ≤ L/2 by omega]
    ring

/-! ## Move the distinguished leg to any requested leg -/

private def swapLeg (t i : ℤ) := if i = t then 0 else if i = 0 then t else i

private theorem swap_bound {k t i : ℤ} (tl : 0 ≤ t) (tu : t < k) (il : 0 ≤ i) (iu : i < k) :
    0 ≤ swapLeg t i ∧ swapLeg t i < k := by unfold swapLeg; split_ifs <;> omega

private def renumber (L t x : ℤ) :=
  if x = 0 then 0 else atRow L (fun i j => L*swapLeg t i+(j+1)) x

private theorem renumber_row {L t i j : ℤ} (hl : 0 < L) (il : 0 ≤ i) (jl : 0 ≤ j) (ju : j < L) :
    renumber L t (L*i+j+1) = L*swapLeg t i+j+1 := by
  have := mul_nonneg hl.le il
  simp only [renumber,show L*i+j+1 ≠ 0 by omega,ite_false,at_row hl jl ju]; omega

private theorem renumber_pos {L k t : ℤ} (hl : 0 < L) (tl : 0 ≤ t) (tu : t < k) :
    BijOn (renumber L t) (Icc 1 (L*k)) (Icc 1 (L*k)) := by
  have h : BijOn (atRow L (fun i j => L*swapLeg t i+(j+1))) (Icc 1 (L*k)) (Icc 1 (L*k)) := by
    apply rows_bij hl
    · intro i j il iu jl ju
      obtain ⟨sl,su⟩ := swap_bound tl tu il iu
      exact block_bound hl sl su (by omega) (by omega)
    · intro i j u v il iu jl ju ul uu vl vu eq
      obtain ⟨b,r⟩ := block_inj hl (r := j+1) (s := v+1) (by omega) (by omega)
        (by omega) (by omega) eq
      unfold swapLeg at b; split_ifs at b <;> exact ⟨by omega,by omega⟩
  apply h.congr
  intro x ⟨xl,xu⟩; simp [renumber,show x ≠ 0 by omega]

private theorem renumber_all {L k t : ℤ} (hl : 0 < L) (tl : 0 ≤ t) (tu : t < k) :
    BijOn (renumber L t) (Icc 0 (L*k)) (Icc 0 (L*k)) := by
  have hp := renumber_pos hl tl tu
  have hz : renumber L t 0 = 0 := by simp [renumber]
  apply bijOn_interval
  · intro x ⟨xl,xu⟩
    by_cases z : x = 0
    · simpa only [z,hz] using (show x ∈ Icc 0 (L*k) from ⟨xl,xu⟩)
    · obtain ⟨l,u⟩ := hp.mapsTo (x := x) ⟨by omega,xu⟩
      exact ⟨by omega,u⟩
  · intro x ⟨xl,xu⟩ y ⟨yl,yu⟩ eq
    by_cases a : x = 0 <;> by_cases b : y = 0
    · omega
    · obtain ⟨l,_⟩ := hp.mapsTo (x := y) ⟨by omega,yu⟩; rw [a,hz] at eq; omega
    · obtain ⟨l,_⟩ := hp.mapsTo (x := x) ⟨by omega,xu⟩; rw [b,hz] at eq; omega
    · exact hp.injOn ⟨by omega,xu⟩ ⟨by omega,yu⟩ eq

private theorem parent_row {L i j : ℤ} (jl : 0 ≤ j) (ju : j < L) :
    parent L (L*i+j+1) = if j = 0 then 0 else L*i+(j-1)+1 := by
  simp only [parent,add_sub_cancel_right,Int.mul_add_emod_self_left,Int.emod_eq_of_lt jl ju]
  split_ifs <;> omega

private theorem renumber_parent {L k t x : ℤ} (hl : 0 < L)
    (hx : x ∈ Icc 1 (L*k)) : renumber L t (parent L x) = parent L (renumber L t x) := by
  obtain ⟨i,j,il,iu,jl,ju,rfl⟩ := coords hl hx
  rw [renumber_row hl il jl ju,parent_row jl ju,parent_row jl ju]
  by_cases z : j = 0
  · simp [z,renumber]
  · simp only [z,ite_false]; exact renumber_row hl il (by omega) (by omega)

/-- Every vertex of the symmetric spider with k legs of length L ≥ 5
can receive 0 in a graceful labeling. -/
theorem zero_rotatable {L k : ℕ} (hL : 5 ≤ L) (hk : 1 ≤ k) (v : ℤ)
    (hv : v ∈ Set.Icc 0 (L*(k : ℤ))) : ∃ f, Graceful L k f ∧ f v = 0 := by
  have hl : 5 ≤ (L : ℤ) := by omega
  have pos : 0 < (L : ℤ) := by omega
  have first (d : ℤ) (hd : d ∈ Icc 0 (L : ℤ)) : ∃ f, Graceful L k f ∧ f d = 0 := by
    simpa only [sub_add_cancel] using first_leg (n := (k:ℤ)-1) hl (by omega) hd
  obtain ⟨vl,vu⟩ := hv
  by_cases z : v = 0
  · subst v; exact first 0 ⟨by omega,by omega⟩
  obtain ⟨i,j,il,iu,jl,ju,eq⟩ := coords pos (show v ∈ Icc 1 (L*(k:ℤ)) from ⟨by omega,vu⟩)
  obtain ⟨f,hf,zero⟩ := first (j+1) ⟨by omega,by omega⟩
  refine ⟨f ∘ renumber L i, ⟨hf.1.comp (renumber_all pos il iu),?_⟩,?_⟩
  · apply (hf.2.comp (renumber_pos pos il iu)).congr
    intro x hx
    simp only [Function.comp_apply,weight,renumber_parent (t := i) pos hx]
  · simpa [Function.comp_apply,eq,renumber_row pos il jl ju,swapLeg] using zero

end SpiderGeneral

