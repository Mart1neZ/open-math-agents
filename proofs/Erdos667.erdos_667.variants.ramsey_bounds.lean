import FormalConjectures.ErdosProblems.«667»

/-!
Assembles the accepted project proofs of the finite Ramsey estimates for Erdős Problem 667.
The top-level reduction is by @DarkWingMcQuack. The lower estimate is from #1310
by @marcusbuffett. The upper-bound reduction and its proofs #1933 and #1936 are
by @steveDOTdigital.
-/

/- 
# Finite graph estimates for the Ramsey bounds of Erdős Problem 667

Credit: @DarkWingMcQuack.
-/

namespace OMA.R_Erdos667_erdos_667_variants_ramsey_bounds_R1

open Erdos667 Filter Real SimpleGraph

/-- Every sufficiently large locally dense graph contains a clique of the lower-bound size. -/
def H1 : Prop :=
  ∀ p : ℕ, 3 ≤ p → ∀ a : ℝ, a < 1 / ((p : ℝ) - 1) →
    ∀ᶠ n : ℕ in atTop, ∃ m : ℕ, m ≤ n ∧ (n : ℝ) ^ a ≤ (m : ℝ) ∧
      ∀ G : SimpleGraph (Fin n), LocallyDense p 1 G → ¬ G.CliqueFree m

/-- Arbitrarily large locally dense graphs exist with clique number at most the upper-bound
size. -/
def H2 : Prop :=
  ∀ p : ℕ, 3 ≤ p → ∀ b : ℝ, 2 / ((p : ℝ) + 1) < b →
    ∃ᶠ n : ℕ in atTop, ∃ (m : ℕ) (G : SimpleGraph (Fin n)),
      (m : ℝ) ≤ (n : ℝ) ^ b ∧ LocallyDense p 1 G ∧ G.CliqueFree (m + 1)

lemma one_le_H (p : ℕ) {n : ℕ} (hn : 1 ≤ n) : 1 ≤ H p 1 n := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  unfold H
  refine Nat.le_findGreatest hn ?_
  intro G _
  rw [cliqueFree_one]
  exact not_isEmpty_of_nonempty _

lemma H_le_of_cliqueFree {p n m : ℕ} {G : SimpleGraph (Fin n)}
    (hDense : LocallyDense p 1 G) (hFree : G.CliqueFree (m + 1)) : H p 1 n ≤ m := by
  classical
  have hSpec : ∀ G' : SimpleGraph (Fin n), LocallyDense p 1 G' →
      ¬ G'.CliqueFree (H p 1 n) := by
    unfold H
    apply Nat.findGreatest_spec (P := fun k ↦
      ∀ G' : SimpleGraph (Fin n), LocallyDense p 1 G' → ¬ G'.CliqueFree k)
      (m := 0) (Nat.zero_le n)
    simp
  by_contra! h
  exact hSpec G hDense (hFree.mono (by omega))

theorem main : H1 → H2 → type_of% @Erdos667.erdos_667.variants.ramsey_bounds := by
  classical
  intro hLower hUpper p hp
  let ratio (n : ℕ) := log (H p 1 n) / log n
  have hLarge : ∀ᶠ n : ℕ in atTop, 1 < n := eventually_gt_atTop 1
  have hNonneg : atTop.IsBoundedUnder (· ≥ ·) ratio := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n in atTop, 0 ≤ ratio n
    filter_upwards [hLarge] with n hn
    have hOne : 1 ≤ (H p 1 n : ℝ) := by exact_mod_cast one_le_H p hn.le
    have hLog : 0 ≤ log (n : ℝ) := log_nonneg (by exact_mod_cast hn.le)
    exact div_nonneg (log_nonneg hOne) hLog
  have hBounded : atTop.IsBoundedUnder (· ≤ ·) ratio := by
    refine ⟨1, ?_⟩
    change ∀ᶠ n in atTop, ratio n ≤ 1
    filter_upwards [hLarge] with n hn
    have hLog : 0 < log (n : ℝ) := log_pos (by exact_mod_cast hn)
    have hHpos : 0 < (H p 1 n : ℝ) := by
      exact_mod_cast (Nat.zero_lt_one.trans_le (one_le_H p hn.le))
    have hHle : (H p 1 n : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.findGreatest_le (P := fun m ↦
        ∀ G : SimpleGraph (Fin n), LocallyDense p 1 G → ¬ G.CliqueFree m) n
    exact (div_le_one hLog).mpr (log_le_log hHpos hHle)
  change 1 / ((p : ℝ) - 1) ≤ liminf ratio atTop ∧
    liminf ratio atTop ≤ 2 / ((p : ℝ) + 1)
  refine ⟨(le_liminf_iff' hBounded.isCoboundedUnder_ge hNonneg).mpr ?_,
    (liminf_le_iff' hBounded.isCoboundedUnder_ge hNonneg).mpr ?_⟩
  · intro a ha
    filter_upwards [hLarge, hLower p hp a ha] with n hn hWitness
    obtain ⟨m, hmn, hPower, hGraph⟩ := hWitness
    have hml : (m : ℝ) ≤ (H p 1 n : ℝ) := by
      exact_mod_cast Nat.le_findGreatest hmn hGraph
    have hnReal : 1 < (n : ℝ) := by exact_mod_cast hn
    have hnPos : 0 < (n : ℝ) := zero_lt_one.trans hnReal
    apply (le_div_iff₀ (log_pos hnReal)).mpr
    rw [← log_rpow hnPos]
    exact log_le_log (rpow_pos_of_pos hnPos _) (hPower.trans hml)
  · intro b hb
    refine ((hUpper p hp b hb).and_eventually hLarge).mono ?_
    rintro n ⟨⟨m, G, hPower, hDense, hFree⟩, hn⟩
    have hHle : (H p 1 n : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast H_le_of_cliqueFree hDense hFree
    have hHpos : 0 < (H p 1 n : ℝ) := by
      exact_mod_cast (Nat.zero_lt_one.trans_le (one_le_H p hn.le))
    have hnReal : 1 < (n : ℝ) := by exact_mod_cast hn
    have hnPos : 0 < (n : ℝ) := zero_lt_one.trans hnReal
    apply (div_le_iff₀ (log_pos hnReal)).mpr
    rw [← log_rpow hnPos]
    exact log_le_log hHpos (hHle.trans hPower)

end OMA.R_Erdos667_erdos_667_variants_ramsey_bounds_R1

/- A finite Ramsey graph criterion and its parameters. -/
-- Credit: @steveDOTdigital
namespace OMA.R_Erdos667_erdos_667_variants_ramsey_bounds_R1_H2_R1
open Erdos667 Filter

-- B is the reciprocal probability of a red edge. The first estimate controls red p-cliques
-- touching any given edge. The second makes blue m-cliques sufficiently rare.
def H1 : Prop := ∀ p n B m : ℕ, (3 ≤ p ∧ p ≤ n ∧ 2 ≤ B ∧ 3 ≤ m ∧ m ≤ n ∧
  64*p^2*n^(p-2) ≤ B^(p.choose 2-1) ∧
  32*(B : ℝ)*(Real.log n+1) ≤ m) →
  ∃ G : SimpleGraph (Fin n), LocallyDense p 1 G ∧ G.CliqueFree (m+1)

-- A strict exponent gap permits integer powers for n, B and m.
def H2 : Prop := ∀ p : ℕ, 3 ≤ p → ∀ b : ℝ, 2/((p : ℝ)+1) < b →
  ∃ᶠ n : ℕ in atTop, ∃ B m : ℕ, (3 ≤ p ∧ p ≤ n ∧ 2 ≤ B ∧ 3 ≤ m ∧ m ≤ n ∧
  64*p^2*n^(p-2) ≤ B^(p.choose 2-1) ∧
  32*(B : ℝ)*(Real.log n+1) ≤ m) ∧ (m : ℝ) ≤ (n : ℝ)^b

theorem main : H1 → H2 → OMA.R_Erdos667_erdos_667_variants_ramsey_bounds_R1.H2 := by
  intro graph parameters p hp b hb
  apply (parameters p hp b hb).mono
  rintro n ⟨B,m,fit,cap⟩
  obtain ⟨G,dense,free⟩ := graph p n B m fit
  exact ⟨m,G,cap,dense,free⟩

end OMA.R_Erdos667_erdos_667_variants_ramsey_bounds_R1_H2_R1

/- Apply the off-diagonal Ramsey recurrence with singleton base cases. -/

open Combinatorics.Diagonal Finset SimpleGraph Filter Real

namespace OMA.RamseyLower

lemma binomial (s t : ℕ) : HasRamseyProperty ((s+t).choose s) (s+1) (t+1) := by
  induction s generalizing t with
  | zero => rw [Nat.choose_zero_right]; exact hasRamseyProperty_one_left (t+1)
  | succ s ih =>
    induction t with
    | zero => rw [Nat.add_zero, Nat.choose_self]; exact hasRamseyProperty_one_right (s+2)
    | succ t iht =>
      have h : HasRamseyProperty (((s+(t+1)).choose s) + ((s+1+t).choose (s+1))) (s+2) (t+2) :=
        HasRamseyProperty.step (ih (t+1)) iht (Nat.choose_pos (by omega))
      rw [show s+1+(t+1) = (s+(t+1))+1 by omega, Nat.choose_succ_succ]
      rw [show s+1+t = s+(t+1) by omega] at h
      intro m c V hV
      exact h c V hV

lemma clique {s t n : ℕ} (h : (s+t).choose s ≤ n) (G : SimpleGraph (Fin n))
    (hd : Erdos667.LocallyDense (s+1) 1 G) : ¬ G.CliqueFree (t+1) := by
  classical
  let c (e : Finset (Fin n)) := decide (G.IsClique (e : Set (Fin n)))
  have cp (x y : Fin n) (hne : x ≠ y) : c {x,y} = true ↔ G.Adj x y := by
    simp [c, hne]
  rcases binomial s t c univ (by simpa using h) with ⟨S,_,hS,hcol⟩ | ⟨S,_,hS,hcol⟩
  · have hempty : G.induce (S : Set (Fin n)) = ⊥ := by
      apply le_bot_iff.mp
      intro x y hxy
      have ha : G.Adj x.val y.val := hxy
      have hh := (cp _ _ ha.ne).mpr ha
      have hfalse := hcol {x.val,y.val} (Finset.insert_subset x.property (Finset.singleton_subset_iff.mpr y.property)) (by simp [ha.ne])
      simp [hh] at hfalse
    have hb := hd S hS
    simp [hempty] at hb
  · apply IsNClique.not_cliqueFree (s := S)
    refine ⟨?_,hS⟩
    intro x hx y hy hne
    exact (cp _ _ hne).mp (hcol {x,y} (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy)) (by simp [hne]))

end OMA.RamseyLower

theorem OMA.RamseyAssembly.lower_bound_estimate : OMA.R_Erdos667_erdos_667_variants_ramsey_bounds_R1.H1 := by
  intro p hp a ha
  obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  let b := 1 / (s : ℝ)
  have hs : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
  have hb : 0 < b := by dsimp [b]; positivity
  have hba : a < b := by simpa [b] using ha
  have tend (d : ℝ) (hd : 0 < d) : Tendsto (fun n : ℕ => (n : ℝ)^d) atTop atTop :=
    (tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop
  filter_upwards [(tend b hb).eventually_ge_atTop 2,
    (tend (b-a) (by linarith)).eventually_ge_atTop 2, eventually_ge_atTop 1] with n hn hd hn1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  let t := ⌊(n : ℝ)^b / 2⌋₊
  have ht : (t : ℝ) ≤ (n : ℝ)^b / 2 := Nat.floor_le (by positivity)
  have ht' : (n : ℝ)^b / 2 < (t : ℝ)+1 := Nat.lt_floor_add_one _
  have hmul : (n : ℝ)^a * (n : ℝ)^(b-a) = (n : ℝ)^b := by
    rw [← Real.rpow_add hnpos]; congr 1; ring
  have hlow : (n : ℝ)^a ≤ (t+1 : ℕ) := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hd (Real.rpow_nonneg hnpos.le a)]
  have hu : ((t+1 : ℕ) : ℝ) ≤ (n : ℝ)^b := by push_cast; linarith
  have hun : t+1 ≤ n := by
    exact_mod_cast hu.trans ((Real.rpow_le_rpow_of_exponent_le hnreal (by
      dsimp [b]; exact (div_le_one (by linarith)).mpr hs)).trans_eq (Real.rpow_one _))
  refine ⟨t+1,hun,hlow,fun G hg => OMA.RamseyLower.clique ?_ G hg⟩
  have he : ((n : ℝ)^b) ^ (s : ℕ) = n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
    have : b * s = 1 := by dsimp [b]; field_simp
    rw [this, Real.rpow_one]
  have hpow : (t+1)^s ≤ n := by
    exact_mod_cast (pow_le_pow_left₀ (by positivity) hu s).trans_eq he
  exact (Nat.add_comm s t ▸ Nat.choose_add_le_add_one_pow t s).trans hpow

/- Avoiding small red cliques in a finite random graph. -/
-- Credit: @steveDOTdigital
namespace OMA.SparseRamsey
open Finset
open scoped Classical

private noncomputable def mass {Ω : Type*} (P : Ω → Prop) : ℝ := Nat.card {a // P a}
private def fixed {E C : Type*} (D : Finset E) (L : Finset C) (f : E → C) :=
  ∀ e ∈ D, f e ∈ L

-- Split a coloring into its coordinates on D and the other coordinates. The condition P
-- is determined by the latter. Every allowed assignment on D has the same number of extensions.
private lemma independent {E C : Type*} [Fintype E] [Fintype C] [Inhabited C]
    (D : Finset E) (L : Finset C) (P : (E → C) → Prop)
    (determined : ∀ f g, (∀ i ∉ D, f i=g i) → (P f ↔ P g)) :
    mass (fun f => P f ∧ fixed D L f) * (Fintype.card C : ℝ)^D.card =
      mass P * (L.card : ℝ)^D.card := by
  classical
  let A := {i // i ∈ D}
  let B := {i // i ∉ D}
  let fill (h : B → C) (i : E) := if hm : i ∈ D then default else h ⟨i,hm⟩
  let tail := {h : B → C // P (fill h)}
  have count (K : Finset C) :
      Nat.card {f : E → C // P f ∧ fixed D K f} = K.card^D.card * Nat.card tail := by
    let equiv : {f : E → C // P f ∧ fixed D K f} ≃ (A → ↥K) × tail := {
      toFun := fun f => (fun e => ⟨f.val e,f.property.2 e e.property⟩,
        ⟨fun i => f.val i,(determined f.val _ (by intro i hi; simp [fill,hi])).mp f.property.1⟩)
      invFun := fun x => by
        let f (i : E) := if hi : i ∈ D then (x.1 ⟨i,hi⟩).val else x.2.val ⟨i,hi⟩
        refine ⟨f,(determined f (fill x.2.val) (by intro i hi; simp [f,fill,hi])).mpr x.2.property,?_⟩
        intro i hi
        simp [f, hi]
      left_inv := fun f => by apply Subtype.ext; funext i; by_cases h : i ∈ D <;> simp [h]
      right_inv := fun x => by
        apply Prod.ext
        · funext i; apply Subtype.ext; simp [i.property]
        · apply Subtype.ext; funext i; simp [i.property] }
    rw [Nat.card_congr equiv,Nat.card_prod,Nat.card_eq_fintype_card (α := A → ↥K),Fintype.card_fun]
    simp [A]
  have eq : Nat.card {f : E → C // P f ∧ fixed D univ f} = Nat.card {f // P f} :=
    Nat.card_congr (Equiv.subtypeEquivRight (by intro f; simp [fixed]))
  have pt := count univ
  rw [eq,card_univ] at pt
  unfold mass
  rw [count L,pt]
  push_cast
  ring

private def avoid {I Ω : Type*} (A : I → Ω → Prop) (S : Finset I) (w : Ω) := ∀ i ∈ S, ¬A i w

private lemma mass_le {Ω : Type*} [Finite Ω] {P Q : Ω → Prop} (incl : ∀ w, P w → Q w) :
    mass P ≤ mass Q := by
  unfold mass
  exact_mod_cast Nat.card_le_card_of_injective
    (fun z : {w // P w} => (⟨z.val,incl _ z.property⟩ : {w // Q w}))
    (fun _ _ h => Subtype.ext (congrArg (fun a : {w // Q w} => a.val) h))

private lemma mass_split {Ω : Type*} [Fintype Ω] (P Q : Ω → Prop) :
    mass (fun w => P w ∧ Q w) + mass (fun w => P w ∧ ¬Q w) = mass P := by
  classical
  let e : {w // P w ∧ Q w} ⊕ {w // P w ∧ ¬Q w} ≃ {w // P w} := {
    toFun := Sum.elim (fun w => ⟨w.val,w.property.1⟩) (fun w => ⟨w.val,w.property.1⟩)
    invFun := fun w => if h : Q w.val then .inl ⟨w.val,w.property,h⟩ else .inr ⟨w.val,w.property,h⟩
    left_inv := by rintro (w|w) <;> simp [w.property.2]
    right_inv := by intro w; by_cases h : Q w.val <;> simp [h] }
  have := Nat.card_congr e
  rw [Nat.card_sum] at this
  unfold mass
  exact_mod_cast this

private lemma avoid_insert {I Ω : Type*} [Fintype Ω] [DecidableEq I] (A : I → Ω → Prop) (i : I) (S : Finset I) :
    mass (fun w => avoid A S w ∧ A i w) + mass (avoid A (insert i S)) = mass (avoid A S) := by
  have e : avoid A (insert i S) = fun w => avoid A S w ∧ ¬A i w := by
    funext w; apply propext; simp [avoid,and_comm]
  rw [e]
  exact mass_split _ _

-- Restore the events of K one by one. Each restored condition keeps fraction c.
private lemma extend_mass {I : Type*} [DecidableEq I] (W : Finset I → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (T K : Finset I) (dis : Disjoint T K)
    (step : ∀ U, U ⊂ T ∪ K → ∀ i ∉ U, c*W U ≤ W (insert i U)) :
    c^K.card*W T ≤ W (T ∪ K) := by
  induction K using Finset.induction_on with
  | empty => simp
  | @insert i K hi ih =>
    have di := Finset.disjoint_insert_right.mp dis
    have ni : i ∉ T ∪ K := by simp [di.1,hi]
    have eq : T ∪ insert i K = insert i (T ∪ K) := by ext; simp
    have st : T ∪ K ⊂ T ∪ insert i K := by rw [eq]; exact Finset.ssubset_insert ni
    have old := ih di.2 (fun U hu => step U (hu.trans st))
    rw [Finset.card_insert_of_notMem hi,pow_succ,eq]
    calc
      _ = c*(c^K.card*W T) := by ring
      _ ≤ c*W (T ∪ K) := mul_le_mul_of_nonneg_left old hc
      _ ≤ _ := step _ st i ni

-- For i outside S, condition first on the events of S not meeting i, where i is
-- independent. Induction bounds the cost of restoring the events that do meet i.
private lemma conditional {I Ω : Type*} [Fintype Ω] [DecidableEq I] (A : I → Ω → Prop)
    (near : I → I → Bool) (D : ℕ) (x β : ℝ) (hx : 0≤x) (hx' : x<1)
    (cap : β ≤ x*(1-x)^D) (count : ∀ i (S : Finset I), i ∉ S → (S.filter (fun j => near i j)).card ≤ D)
    (indep : ∀ i (S : Finset I), i ∉ S →
      mass (fun w => avoid A S w ∧ A i w) ≤ β * mass (avoid A (S.filter fun j => !(near i j)))):
    ∀ (S : Finset I) i, i ∉ S → (1-x)*mass (avoid A S) ≤ mass (avoid A (insert i S)) := by
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro i hi
    let T := S.filter (fun j => !(near i j))
    let K := S.filter (fun j => near i j)
    have dis : Disjoint T K := by
      apply Finset.disjoint_left.mpr
      intro j ht hk
      have a := (mem_filter.mp ht).2
      have b := (mem_filter.mp hk).2
      simp [b] at a
    have both : T ∪ K = S := by ext j; by_cases a : near i j <;> simp [T,K,a]
    have c0 : 0 ≤ 1-x := by linarith
    have restore := extend_mass (fun s => mass (avoid A s)) c0 T K dis
      (fun U hu j hj => ih U (both ▸ hu) j hj)
    rw [both] at restore
    have pD : (1-x)^D ≤ (1-x)^K.card := pow_le_pow_of_le_one c0 (by linarith) (count i S hi)
    have cap' := cap.trans (mul_le_mul_of_nonneg_left pD hx)
    have tn : 0 ≤ mass (avoid A T) := Nat.cast_nonneg _
    have h1 := mul_le_mul_of_nonneg_right cap' tn
    have h2 := mul_le_mul_of_nonneg_left restore hx
    have prob := indep i S hi
    change _ ≤ β * mass (avoid A T) at prob
    have split := avoid_insert A i S
    nlinarith only [h1,h2,prob,split]

private noncomputable def touch {E : Type*} (D T : Finset E) : Bool :=
  decide (¬Disjoint D T)

private lemma color_bound {E C I : Type*} [Fintype E] [Fintype C] [Inhabited C]
    (support : I → Finset E) (labels : I → Finset C) (S : Finset I) (D : Finset E) (L : Finset C) :
    let A := fun i => fixed (support i) (labels i)
    let T := S.filter (fun j => !(touch D (support j)))
    mass (fun f => avoid A S f ∧ fixed D L f) * (Fintype.card C : ℝ)^D.card ≤
      mass (avoid A T) * (L.card : ℝ)^D.card := by
  classical
  let A := fun i => fixed (support i) (labels i)
  let T := S.filter (fun j => !(touch D (support j)))
  have det (f g : E → C) (eq : ∀ i ∉ D, f i=g i) : avoid A T f ↔ avoid A T g := by
    have same (j : I) (hj : j ∈ T) : A j f ↔ A j g := by
      have dis : Disjoint D (support j) := by simpa [touch] using (mem_filter.mp hj).2
      have v (i : E) (hi : i ∈ support j) : f i=g i := eq i (fun h => Finset.disjoint_left.mp dis h hi)
      constructor <;> intro h i hi
      · rw [←v i hi]; exact h i hi
      · rw [v i hi]; exact h i hi
    exact ⟨fun h j hj => (same j hj).not.mp (h j hj),fun h j hj => (same j hj).not.mpr (h j hj)⟩
  have sub : mass (fun f => avoid A S f ∧ fixed D L f) ≤ mass (fun f => avoid A T f ∧ fixed D L f) :=
    mass_le (fun _ h => ⟨fun j hj => h.1 j (mem_filter.mp hj).1,h.2⟩)
  exact (mul_le_mul_of_nonneg_right sub (by positivity)).trans_eq (independent D L _ det)

private lemma overlap_count {n p : ℕ} (U : Finset (Fin n)) (S : Finset {s : Finset (Fin n) // s.card=p}) :
    (S.filter fun j => touch (U.powersetCard 2) (j.val.powersetCard 2)).card ≤ U.card^2*n^(p-2) := by
  classical
  let K := S.filter (fun j => touch (U.powersetCard 2) (j.val.powersetCard 2))
  let pairs := U.powersetCard 2
  let rest := (univ : Finset (Fin n)).powersetCard (p-2)
  let union := fun et : Finset (Fin n) × Finset (Fin n) => et.1 ∪ et.2
  have sub : K.image Subtype.val ⊆ (pairs ×ˢ rest).image union := by
    rintro x hx
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hx
    have ov : ¬Disjoint (U.powersetCard 2) (j.val.powersetCard 2) := by simpa [touch] using (mem_filter.mp hj).2
    obtain ⟨v,hv,hjv⟩ := not_disjoint_iff.mp ov
    obtain ⟨vj,vc⟩ := mem_powersetCard.mp hjv
    have rem : j.val \ v ∈ rest := mem_powersetCard.mpr ⟨subset_univ _,by rw [card_sdiff_of_subset vj,j.property,vc]⟩
    exact mem_image.mpr ⟨(v,j.val \ v),mem_product.mpr ⟨hv,rem⟩,Finset.union_sdiff_of_subset vj⟩
  calc
    _ = (K.image Subtype.val).card := (card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ ((pairs ×ˢ rest).image union).card := card_le_card sub
    _ ≤ pairs.card*rest.card := by rw [←card_product]; exact card_image_le
    _ ≤ _ := by simpa [pairs,rest] using Nat.mul_le_mul (Nat.choose_le_pow U.card 2) (Nat.choose_le_pow n (p-2))

private lemma blank {Ω I : Type*} [Fintype Ω] [Nonempty Ω] (A : I → Ω → Prop) :
    0 < mass (avoid A ∅) := by
  have : Nonempty {w // avoid A ∅ w} := ⟨⟨Classical.arbitrary Ω,by simp [avoid]⟩⟩
  unfold mass
  exact_mod_cast (Nat.card_pos (α := {w // avoid A ∅ w}))

private lemma union_bound {Ω I : Type*} [Fintype Ω] (A : I → Ω → Prop) (P : Ω → Prop) (S : Finset I) :
    mass (fun w => P w ∧ ∃ i ∈ S, A i w) ≤ ∑ i ∈ S, mass (fun w => P w ∧ A i w) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have : IsEmpty {w // P w ∧ ∃ i ∈ (∅ : Finset I), A i w} :=
      ⟨fun w => by simpa using w.property.2⟩
    simp [mass]
  | @insert i T hi ih =>
    rw [sum_insert hi]
    let Q := fun w => P w ∧ ∃ j ∈ insert i T, A j w
    have eq := mass_split Q (A i)
    have a : mass (fun w => Q w ∧ A i w) ≤ mass (fun w => P w ∧ A i w) := mass_le (fun _ h => ⟨h.1.1,h.2⟩)
    have b : mass (fun w => Q w ∧ ¬A i w) ≤ mass (fun w => P w ∧ ∃ j ∈ T, A j w) := by
      apply mass_le
      rintro w ⟨⟨pw,j,hj,aj⟩,na⟩
      exact ⟨pw,j,(mem_insert.mp hj).resolve_left (fun e => na (e ▸ aj)),aj⟩
    exact eq.ge.trans (add_le_add a (b.trans ih))

private lemma bernoulli (c : ℝ) (_hc : 0≤c) (hc' : c≤1) (k : ℕ) : 1-(k:ℝ)*c ≤ (1-c)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ,Nat.cast_succ]
    nlinarith only [mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hc'),mul_nonneg (Nat.cast_nonneg k) (sq_nonneg c)]

private lemma log_keep (x : ℝ) (hx : 0≤x) (half : x≤1/2) : -2*x ≤ Real.log (1-x) := by
  have pos : 0<1-x := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr pos)
  rw [Real.log_inv] at h
  have inv : (1-x)⁻¹ ≤ 1+2*x := (inv_le_iff_one_le_mul₀ pos).mpr (by
    nlinarith [mul_nonneg hx (show 0≤1-2*x by linarith)])
  linarith

private lemma estimates (p n B m : ℕ) (hp : 3≤p) (pn : p≤n) (hb : 2≤B) (hm : 3≤ m)
    (degree : 64*p^2*n^(p-2) ≤ B^(p.choose 2-1))
    (size : 32*(B:ℝ)*(Real.log n+1) ≤ m) :
    let β := 1/(B:ℝ)^(p.choose 2)
    0<β ∧ 2*β≤1/2 ∧ β ≤ 2*β*(1-2*β)^(p^2*n^(p-2)) ∧
    ∀ k : ℕ, k≤ m^2*n^(p-2) →
      (n:ℝ)^m * (((B:ℝ)-1)/B)^(m.choose 2) < (1-2*β)^k := by
  let z := (B:ℝ)^(p.choose 2)
  let a := (n:ℝ)^(p-2)
  let d := p^2*n^(p-2)
  have B2 : (2:ℝ)≤B := by exact_mod_cast hb
  have p3 : (3:ℝ)≤p := by exact_mod_cast hp
  have m3 : (3:ℝ)≤ m := by exact_mod_cast hm
  have a1 : 1≤a := one_le_pow₀ (by exact_mod_cast (show 1≤n by omega))
  have bz : 0<(B:ℝ) := by linarith
  have zpos : 0<z := pow_pos bz _
  have hdeg : 64*(p:ℝ)^2*a ≤ (B:ℝ)^(p.choose 2-1) := by dsimp [a]; exact_mod_cast degree
  have rpos := Nat.choose_pos (show 2≤p by omega)
  have eq : (B:ℝ)^(p.choose 2-1)*(B:ℝ)=z := by rw [←pow_succ,Nat.sub_add_cancel rpos]
  have total : 64*(p:ℝ)^2*a*B ≤ z := (mul_le_mul_of_nonneg_right hdeg bz.le).trans_eq eq
  have dre : (d:ℝ)=(p:ℝ)^2*a := by simp [d,a]
  have p1 : 1≤(p:ℝ)^2 := one_le_pow₀ (by linarith)
  have d1 : 1≤(d:ℝ) := by rw [dre]; exact one_le_mul_of_one_le_of_one_le p1 a1
  have rel : 64*(d:ℝ)*B≤z := by rw [dre]; linarith only [total]
  have h4 : 4≤z := by nlinarith [mul_le_mul_of_nonneg_left B2 (by positivity : 0≤(d:ℝ))]
  have hz : 0 < 1/z := by positivity
  have half : 2*(1/z) ≤ 1/2 := by rw [←mul_div_assoc, mul_one]; apply (div_le_iff₀ zpos).mpr; linarith
  have tiny : (d:ℝ)*(2*(1/z)) ≤ 1/2 := by
    rw [show (d:ℝ)*(2*(1/z))=2*d/z by ring]
    apply (div_le_iff₀ zpos).mpr
    nlinarith [mul_le_mul_of_nonneg_left B2 (by positivity : 0≤(d:ℝ))]
  change 0<1/z ∧ _ ∧ _ ∧ _
  refine ⟨hz,half,?_,?_⟩
  · have bern := bernoulli (2*(1/z)) (by positivity) (by linarith) d
    change 1/z ≤ 2*(1/z)*(1-2*(1/z))^d
    have hh : (1:ℝ)/2 ≤ (1-2*(1/z))^d := by linarith only [bern,tiny]
    nlinarith only [mul_le_mul_of_nonneg_left hh hz.le]
  · intro k hk
    have cap : (k:ℝ)≤(m:ℝ)^2*a := by dsimp [a]; exact_mod_cast hk
    have un : 0<((B:ℝ)-1)/B := div_pos (by linarith) bz
    have keep : 0<1-2*(1/z) := by linarith
    have nn : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
    apply (Real.log_lt_log_iff (mul_pos (pow_pos nn _) (pow_pos un _)) (pow_pos keep _)).mp
    rw [Real.log_mul (pow_pos nn _).ne' (pow_pos un _).ne',Real.log_pow,Real.log_pow,Real.log_pow]
    have lb := log_keep (2*(1/z)) (by positivity) half
    have lu := Real.log_le_sub_one_of_pos un
    have eu : ((B:ℝ)-1)/B-1 = -(1/B) := by field_simp; ring
    rw [eu] at lu
    have right := mul_le_mul_of_nonneg_left lb (Nat.cast_nonneg k)
    have left := mul_le_mul_of_nonneg_left lu (Nat.cast_nonneg (m.choose 2))
    have mpos : 0<(m:ℝ) := by linarith
    have term : 32*(m:ℝ)*Real.log n*B ≤ (m:ℝ)^2 := by
      nlinarith only [mul_le_mul_of_nonneg_left size mpos.le,mul_nonneg mpos.le bz.le]
    have cb : 64*a*B ≤ z := by
      have da : a ≤ (d:ℝ) := by rw [dre]; nlinarith only [mul_le_mul_of_nonneg_right p1 (le_trans (by norm_num) a1)]
      nlinarith only [mul_le_mul_of_nonneg_right da bz.le,rel]
    have err : 64*(k:ℝ)*B/z ≤ (m:ℝ)^2 := by
      apply (div_le_iff₀ zpos).mpr
      nlinarith only [mul_le_mul_of_nonneg_right cap bz.le,mul_le_mul_of_nonneg_left cb (sq_nonneg (m:ℝ))]
    have comb := Nat.add_one_mul_choose_eq (m-1) 1
    rw [Nat.sub_add_cancel (by omega : 1≤ m),Nat.choose_one_right] at comb
    have mc : (m:ℝ)*((m:ℝ)-1) = (m.choose 2 : ℝ)*2 := by
      have hcast := congrArg (fun v : ℕ => (v:ℝ)) comb
      simpa only [Nat.cast_mul,Nat.cast_sub (show 1≤ m by omega),Nat.cast_one,Nat.reduceAdd,Nat.cast_ofNat] using hcast
    have gap : (m:ℝ)*Real.log n*B + 4*(k:ℝ)*B/z < m.choose 2 := by
      rw [div_eq_mul_inv] at err ⊢
      nlinarith only [term,err,mc,m3,mul_le_mul_of_nonneg_left m3 mpos.le]
    have final : (m:ℝ)*Real.log n + (m.choose 2 : ℝ)*(-(1/B)) < (k:ℝ)*(-2*(2*(1/z))) := by
      apply (mul_lt_mul_iff_left₀ bz).mp
      field_simp [bz.ne',zpos.ne'] at gap ⊢
      nlinarith only [gap]
    linarith only [left,right,final]

private lemma coloring (p n B m : ℕ)
    (hp : 3 ≤ p) (pn : p ≤ n) (hb : 2 ≤ B) (hm : 3 ≤ m) (mn : m ≤ n)
    (degree : 64*p^2*n^(p-2) ≤ B^(p.choose 2-1))
    (size : 32*(B:ℝ)*(Real.log n+1) ≤ m) :
    ∃ G : SimpleGraph (Fin n), Erdos667.LocallyDense p 1 G ∧ G.CliqueFree (m+1) := by
  classical
  have : NeZero B := ⟨by omega⟩
  let E := Finset (Fin n)
  let Ω := E → Fin B
  let I := {s : E // s.card=p}
  let support (j : I) := j.val.powersetCard 2
  let red := ({0} : Finset (Fin B))
  let blue := (univ : Finset (Fin B)).erase 0
  let A (j : I) := fixed (support j) red
  let adjacent (i j : I) := touch (support i) (support j)
  let W (S : Finset I) := mass (avoid A S)
  let β := 1/(B:ℝ)^(p.choose 2)
  let x := 2*β
  let d := p^2*n^(p-2)
  have Bpos : 0<(B:ℝ) := by exact_mod_cast (show 0<B by omega)
  obtain ⟨βpos,half,redEst,blueEst⟩ := estimates p n B m hp pn hb hm degree size
  change 0<β at βpos
  change x ≤ 1/2 at half
  have x0 : 0 ≤ x := by dsimp [x]; linarith
  have x1 : x < 1 := by linarith
  have nearby (i : I) (S : Finset I) (_ : i ∉ S) :
      (S.filter (fun j => adjacent i j)).card ≤ d := by
    simpa [d,i.property] using overlap_count i.val S
  have ind (i : I) (S : Finset I) (_ : i ∉ S) :
      mass (fun f => avoid A S f ∧ A i f) ≤ β * W (S.filter fun j => !(adjacent i j)) := by
    let T := S.filter fun j => !(adjacent i j)
    have ev := color_bound support (fun _ => red) S (support i) red
    change mass (fun f => avoid A S f ∧ A i f) * (Fintype.card (Fin B) : ℝ)^(support i).card ≤
      W T * (red.card : ℝ)^(support i).card at ev
    have sc : (support i).card = p.choose 2 := by simp [support,i.property]
    simp only [Fintype.card_fin,sc,red,card_singleton,Nat.cast_one,one_pow,mul_one] at ev
    have bd := (le_div_iff₀ (pow_pos Bpos _)).mpr ev
    exact bd.trans_eq (by dsimp [β,T]; ring)
  have step := conditional A adjacent d x β x0 x1 redEst nearby ind
  let S := (univ : Finset I)
  have total : 0<W S := by
    have h := extend_mass W (sub_nonneg.mpr x1.le) ∅ S (by simp) (fun U _ i hi => step U i hi)
    simpa using lt_of_lt_of_le (mul_pos (pow_pos (sub_pos.mpr x1) _) (blank A)) h
  let family := (univ : Finset (Fin n)).powersetCard m
  let event (U : E) := fixed (U.powersetCard 2) blue
  have per (U : E) (hU : U ∈ family) :
      mass (fun f => avoid A S f ∧ event U f) < W S / (n:ℝ)^m := by
    let K := S.filter (fun j => touch (U.powersetCard 2) (support j))
    let T := S.filter (fun j => !(touch (U.powersetCard 2) (support j)))
    have dis : Disjoint T K := by
      apply Finset.disjoint_left.mpr; intro j ht hk
      have a := (mem_filter.mp ht).2
      simp [(mem_filter.mp hk).2] at a
    have both : T ∪ K = S := by ext j; by_cases h : touch (U.powersetCard 2) (support j) <;> simp [T,K,h]
    have restore := extend_mass W (sub_nonneg.mpr x1.le) T K dis (fun V _ j hj => step V j hj)
    rw [both] at restore
    have wt : 0 < W T := by
      have u := mass_le (fun (w : Ω) (h : avoid A S w) => (show avoid A T w from fun j hj => h j (mem_filter.mp hj).1))
      exact total.trans_le u
    have cardU := (mem_powersetCard.mp hU).2
    have cap : K.card ≤ m^2*n^(p-2) := by simpa [K,support,cardU] using overlap_count U S
    have gb := blueEst K.card cap
    change (n:ℝ)^m*(((B:ℝ)-1)/B)^(m.choose 2) < (1-x)^K.card at gb
    have raw := color_bound support (fun _ => red) S (U.powersetCard 2) blue
    let bad := mass (fun f => avoid A S f ∧ event U f)
    change bad * (Fintype.card (Fin B):ℝ)^((U.powersetCard 2).card) ≤ W T * (blue.card:ℝ)^((U.powersetCard 2).card) at raw
    have bc : (blue.card:ℝ)=(B:ℝ)-1 := by
      simp [blue,Nat.cast_sub (by omega : 1≤B)]
    simp only [Fintype.card_fin,card_powersetCard,cardU,bc] at raw
    have bd : bad ≤ W T * (((B:ℝ)-1)/B)^(m.choose 2) := by
      rw [div_pow,←mul_div_assoc]; exact (le_div_iff₀ (pow_pos Bpos _)).mpr raw
    have np : 0<(n:ℝ)^m := pow_pos (by exact_mod_cast (show 0<n by omega)) _
    apply (lt_div_iff₀ np).mpr
    calc
      bad * (n:ℝ)^m ≤ (W T*(((B:ℝ)-1)/B)^(m.choose 2))*(n:ℝ)^m := mul_le_mul_of_nonneg_right bd np.le
      _ = ((n:ℝ)^m*(((B:ℝ)-1)/B)^(m.choose 2))*W T := by ring
      _ < _ := mul_lt_mul_of_pos_right gb wt
      _ ≤ _ := restore
  have upper := union_bound event (avoid A S) family
  have fam : family.Nonempty := by
    obtain ⟨s,h,c⟩ := exists_subset_card_eq (s := (univ : Finset (Fin n))) (by simpa using mn)
    exact ⟨s,mem_powersetCard.mpr ⟨h,c⟩⟩
  have fc : (family.card : ℝ) ≤ (n:ℝ)^m := by
    exact_mod_cast (show family.card ≤ n^m by simpa [family] using Nat.choose_le_pow n m)
  have npos : 0<(n:ℝ)^m := pow_pos (by exact_mod_cast (show 0<n by omega)) _
  have bound : mass (fun w => avoid A S w ∧ ∃ U ∈ family, event U w) < W S := by
    have strict := Finset.sum_lt_sum_of_nonempty fam per
    apply upper.trans_lt (lt_of_lt_of_le strict ?_)
    rw [sum_const,nsmul_eq_mul,←mul_div_assoc]
    apply (div_le_iff₀ npos).mpr
    nlinarith only [mul_le_mul_of_nonneg_right fc total.le]
  have ex : ∃ w : Ω, avoid A S w ∧ ¬∃ U ∈ family, event U w := by
    by_contra! h
    have incl : mass (avoid A S) ≤ mass (fun w => avoid A S w ∧ ∃ U ∈ family, event U w) :=
      mass_le (fun w hw => ⟨hw,h w hw⟩)
    exact (not_lt_of_ge incl) bound
  obtain ⟨w,redFree,blueFree⟩ := ex
  let G : SimpleGraph (Fin n) := {
    Adj := fun a b => a≠b ∧ w {a,b}≠0
    symm := ⟨fun a b h => ⟨h.1.symm,by simpa [Finset.pair_comm b a] using h.2⟩⟩
    loopless := ⟨fun _ h => h.1 rfl⟩ }
  refine ⟨G,?_,?_⟩
  · intro s hs
    have no := redFree (⟨s,hs⟩ : I) (mem_univ _)
    change ¬∀ v ∈ s.powersetCard 2, w v ∈ red at no
    push Not at no
    obtain ⟨v,hv,un⟩ := no
    obtain ⟨sub,two⟩ := mem_powersetCard.mp hv
    obtain ⟨a,b,ne,rfl⟩ := card_eq_two.mp two
    have a' : a ∈ s := sub (by simp)
    have b' : b ∈ s := sub (by simp)
    have pair : (G.induce s).Adj ⟨a,a'⟩ ⟨b,b'⟩ := ⟨ne,by simpa [red] using un⟩
    exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨s((⟨a,a'⟩ : ↥s),(⟨b,b'⟩ : ↥s)),pair⟩
  · apply SimpleGraph.CliqueFree.mono (m:=m) (by omega)
    intro s hs
    obtain ⟨cl,sz⟩ := G.isNClique_iff.mp hs
    apply blueFree
    refine ⟨s,mem_powersetCard.mpr ⟨subset_univ _,sz⟩,?_⟩
    intro v hv
    obtain ⟨sub,two⟩ := mem_powersetCard.mp hv
    obtain ⟨a,b,ne,rfl⟩ := card_eq_two.mp two
    have adj := cl (show a ∈ (s:Set _) from sub (by simp)) (show b ∈ (s:Set _) from sub (by simp)) ne
    exact mem_erase.mpr ⟨adj.2,mem_univ _⟩

end OMA.SparseRamsey

theorem OMA.RamseyAssembly.sparse_coloring_estimate : OMA.R_Erdos667_erdos_667_variants_ramsey_bounds_R1_H2_R1.H1 := by
  rintro p n B m ⟨hp,pn,hb,hm,mn,degree,size⟩
  exact OMA.SparseRamsey.coloring p n B m hp pn hb hm mn degree size

/- Integer parameters for the sparse Ramsey construction. -/
-- Credit: @steveDOTdigital
namespace OMA.RamseyParameters
open Filter

-- Integer powers leave one full power of t for each strict inequality.
private lemma edge_exponent (p : ℕ) (hp : 3 ≤ p) :
    (p+1)*(p-2) = 2*(p.choose 2-1) ∧ 1 ≤ p.choose 2-1 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hp
  have h := Nat.add_one_mul_choose_eq (j+2) 1
  simp only [Nat.choose_one_right] at h
  have he : 3+j=j+2+1 := by omega
  rw [he]
  have sz : 2 ≤ (j+2+1).choose 2 := by nlinarith only [h,Nat.zero_le (j*j),Nat.zero_le j]
  have sub := Nat.sub_add_cancel (show 1 ≤ (j+2+1).choose 2 by omega)
  constructor
  · rw [show j+2+1-2=j+1 by omega]
    nlinarith only [h,sub]
  · omega

private lemma parameters (p : ℕ) (hp : 3 ≤ p) (b : ℝ) (hb : 2/((p:ℝ)+1)<b) :
    ∃ᶠ n : ℕ in atTop, ∃ B m : ℕ, (3 ≤ p ∧ p ≤ n ∧ 2 ≤ B ∧ 3 ≤ m ∧ m ≤ n ∧
  64*p^2*n^(p-2) ≤ B^(p.choose 2-1) ∧
  32*(B : ℝ)*(Real.log n+1) ≤ m) ∧ (m : ℝ) ≤ (n : ℝ)^b := by
  have gap : 0 < ((p:ℝ)+1)*b-2 := by
    have h := (div_lt_iff₀ (show 0<(p:ℝ)+1 by positivity)).mp hb
    linarith
  obtain ⟨s,hs⟩ := exists_nat_gt (2/(((p:ℝ)+1)*b-2))
  have hs' := (div_lt_iff₀ gap).mp hs
  have s0 : 0<s := by
    by_contra! h
    have hz : s=0 := by omega
    rw [hz] at hs'
    norm_num at hs'
  let d := (p+1)*s
  let e := 2*s+1
  let f := 2*s+2
  have dpos : 0<d := Nat.mul_pos (by omega) s0
  have fd : f ≤ d := by dsimp [f,d]; nlinarith [Nat.mul_le_mul_right s hp]
  have fR : (f:ℝ) ≤ (d:ℝ)*b := by dsimp [f,d]; push_cast; nlinarith only [hs']
  rw [Filter.frequently_atTop]
  intro M
  let x := M+128*(d+1)+64*p^2+p+3
  let t := x^2
  have xle : x ≤ t := Nat.le_self_pow (by decide : 2 ≠ 0) x
  have big : M ≤ x ∧ p ≤ x ∧ 3 ≤ x ∧ 64*p^2 ≤ x ∧ 128*(d+1) ≤ x := by dsimp [x]; omega
  have tn : t ≤ t^d := Nat.le_self_pow dpos.ne' _
  have be : t ≤ t^e := Nat.le_self_pow (by dsimp [e]; omega) _
  have fm : t ≤ t^f := Nat.le_self_pow (by dsimp [f]; omega) _
  have edge := edge_exponent p hp
  let r := p.choose 2-1
  have expEq : r+d*(p-2)=e*r := by
    calc
      _ = r+s*((p+1)*(p-2)) := by dsimp [d]; ring
      _ = _ := by rw [edge.1]; dsimp [e,r]; ring
  have compare : 64*p^2*(t^d)^(p-2) ≤ (t^e)^r := by
    rw [←pow_mul t d (p-2),←pow_mul t e r,←expEq,pow_add]
    exact Nat.mul_le_mul_right _ ((big.2.2.2.1.trans xle).trans (Nat.le_self_pow (Nat.ne_of_gt edge.2) t))
  have x0 : 0<(x:ℝ) := by exact_mod_cast (show 0<x by omega)
  have dt : 128*((d:ℝ)+1) ≤ x := by exact_mod_cast big.2.2.2.2
  have logt : Real.log (t:ℝ) ≤ 2*(x:ℝ) := by
    have := Real.log_le_sub_one_of_pos x0
    dsimp [t]; rw [Nat.cast_pow,Real.log_pow]; norm_num; linarith
  have tcap : 32*((d:ℝ)*Real.log (t:ℝ)+1) ≤ t := by
    have a := mul_le_mul_of_nonneg_left logt (by positivity : 0 ≤ (d:ℝ))
    have x3 : (3:ℝ) ≤ x := by exact_mod_cast big.2.2.1
    have h := mul_le_mul_of_nonneg_right dt x0.le
    calc
      _ ≤ (x:ℝ)^2 := by nlinarith only [a,h,x3,mul_nonneg (by positivity : 0≤(d:ℝ)) x0.le]
      _ = _ := by simp [t]
  refine ⟨t^d,by omega,t^e,t^f,⟨hp,by omega,by omega,by omega,
    Nat.pow_le_pow_right (by omega : 0<t) fd,compare,?_⟩,?_⟩
  · push_cast
    rw [Real.log_pow,show f=e+1 by rfl,pow_succ (t:ℝ) e]
    nlinarith only [mul_le_mul_of_nonneg_left tcap (by positivity : 0 ≤ (t:ℝ)^e)]
  · push_cast
    rw [←Real.rpow_natCast_mul (by positivity)]
    rw [←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ t by omega)) fR

end OMA.RamseyParameters

theorem OMA.RamseyAssembly.integer_parameters : OMA.R_Erdos667_erdos_667_variants_ramsey_bounds_R1_H2_R1.H2 := OMA.RamseyParameters.parameters

theorem OMA.solution : type_of% @Erdos667.erdos_667.variants.ramsey_bounds := by
  apply OMA.R_Erdos667_erdos_667_variants_ramsey_bounds_R1.main
  · exact OMA.RamseyAssembly.lower_bound_estimate
  · exact OMA.R_Erdos667_erdos_667_variants_ramsey_bounds_R1_H2_R1.main
      OMA.RamseyAssembly.sparse_coloring_estimate
      OMA.RamseyAssembly.integer_parameters
