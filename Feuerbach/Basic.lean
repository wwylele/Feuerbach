import Mathlib
import Archive.Wiedijk100Theorems.HeronsFormula
import Feuerbach.Aristotle1

noncomputable section


open Affine Simplex Real EuclideanGeometry RealInnerProductSpace

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

namespace EuclideanGeometry

theorem dist_affineCombination_left {w : Fin 3 → ℝ} (hw : ∑ i, w i = 1) (p : Fin 3 → P)
    (q : P) :
    (dist (Finset.affineCombination ℝ Finset.univ p w) q) ^ 2 =
    w 0 * dist (p 0) q ^ 2 + w 1 * dist (p 1) q ^ 2 + w 2 * dist (p 2) q ^ 2 -
    (w 1 * w 2 * dist (p 1) (p 2) ^ 2 + w 2 * w 0 * dist (p 2) (p 0) ^ 2
      + w 0 * w 1 * dist (p 0) (p 1) ^ 2)
    := by
  have h (i j : Fin 3) : 2 * w i * w j * ⟪q -ᵥ p i, q -ᵥ p j⟫ =
      w i * w j * dist (p i) q ^ 2 + w i * w j * dist (p j) q ^ 2
      -w i * w j * dist (p i) (p j) ^ 2 := by
    simp_rw [dist_eq_norm_vsub']
    rw [← vsub_sub_vsub_cancel_left (p j) (p i) q]
    simp_rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
      real_inner_comm (q -ᵥ p j) (q -ᵥ p i)]
    ring
  have hw' : w 0 + w 1 + w 2 = 1 := by
    simpa [Finset.sum, ← add_assoc] using hw
  calc
    _ = ‖q -ᵥ Finset.affineCombination ℝ Finset.univ p w‖ ^ 2 := by rw [dist_eq_norm_vsub']
    _ = ‖∑ i, w i • (q -ᵥ p i)‖ ^ 2 := by
      rw [Finset.sum_smul_const_vsub_eq_vsub_affineCombination _ _ _ _ hw]
    _ = ‖w 0 • (q -ᵥ p 0) + w 1 • (q -ᵥ p 1) + w 2 • (q -ᵥ p 2)‖ ^ 2 := by
      simp [Finset.sum, add_assoc]
    _ = w 0 ^ 2 * (dist (p 0) q) ^ 2 + w 1 ^ 2 * (dist (p 1) q) ^ 2
        + w 2 ^ 2 * (dist (p 2) q) ^ 2
        + 2 * w 0 * w 1 * ⟪q -ᵥ p 0, q -ᵥ p 1⟫ + 2 * w 1 * w 2 * ⟪q -ᵥ p 1, q -ᵥ p 2⟫
        + 2 * w 2 * w 0 * ⟪q -ᵥ p 2, q -ᵥ p 0⟫ := by
      simp_rw [dist_eq_norm_vsub', ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
        real_inner_smul_left, real_inner_smul_right,
        real_inner_comm (q -ᵥ p 1) (q -ᵥ p 0), real_inner_comm (q -ᵥ p 2) (q -ᵥ p 1),
        real_inner_comm (q -ᵥ p 0) (q -ᵥ p 2)]
      ring
    _ = w 0 * (w 0 + w 1 + w 2) * (dist (p 0) q) ^ 2 + w 1 * (w 0 + w 1 + w 2) * (dist (p 1) q) ^ 2
        + w 2 * (w 0 + w 1 + w 2) * (dist (p 2) q) ^ 2 -
        (w 1 * w 2 * dist (p 1) (p 2) ^ 2 + w 2 * w 0 * dist (p 2) (p 0) ^ 2
        + w 0 * w 1 * dist (p 0) (p 1) ^ 2) := by
      rw [h 0 1, h 1 2, h 2 0]
      ring
    _ = _ := by simp [hw']

end EuclideanGeometry

namespace Affine

namespace Simplex

def volume {n : ℕ} (s : Affine.Simplex ℝ P n) : ℝ :=
  match n with
  | 0 => 1
  | n + 1 => ((n + 1 : ℕ) : ℝ)⁻¹ * s.height 0 * (s.faceOpposite 0).volume

theorem volume_pos {n : ℕ} (s : Affine.Simplex ℝ P n) : 0 < s.volume := by
  induction n with
  | zero => simp [volume]
  | succ n ih =>
    rw [volume]
    apply mul_pos
    · positivity
    · apply ih

open Qq Mathlib.Meta.Positivity in
@[positivity volume _]
meta def evalVolume : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@volume $V $P $i1 $i2 $i3 $i4 $n $s) =>
    assertInstancesCommute
    return .positive q(volume_pos $s)
  | _, _, _ => throwError "not Simplex.volume"

def base {n : ℕ} [NeZero n] (s : Affine.Simplex ℝ P n) (i : Fin (n + 1)) :=
  (s.faceOpposite i).volume

theorem base_pos {n : ℕ} [NeZero n] (s : Affine.Simplex ℝ P n) (i : Fin (n + 1)) :
    0 < s.base i := volume_pos _

open Qq Mathlib.Meta.Positivity in
@[positivity base _ _]
meta def evalBase : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@base $V $P $i1 $i2 $i3 $i4 $n $hn $s $i) =>
    assertInstancesCommute
    return .positive q(base_pos $s $i)
  | _, _, _ => throwError "not Simplex.volume"

theorem volume_eq_one (s : Affine.Simplex ℝ P 0) : s.volume = 1 := rfl

theorem volume_eq_dist (s : Affine.Simplex ℝ P 1) :
    s.volume = dist (s.points 0) (s.points 1) := by
  simp [volume, height, altitudeFoot]

theorem volume_eq_height_mul_base₀ {n : ℕ} [NeZero n] (s : Affine.Simplex ℝ P n) :
    s.volume = (n : ℝ)⁻¹ * s.height 0 * s.base 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_add_one_eq.mpr (Nat.pos_of_neZero n)
  rw [volume, base]

def excenterWeightsUnnormBase {n : ℕ} [NeZero n] (s : Simplex ℝ P n)
    (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) :=
  (if i ∈ signs then -1 else 1) * s.base i

end Simplex


local notation "w[" s ", " signs ", " i "]" => excenterWeightsUnnormBase s signs i

namespace Triangle


theorem height_eq_sin_mul (s : Affine.Triangle ℝ P) (i : Fin 3) :
    s.height i = sin (∠ (s.points i) (s.points (i + 1)) (s.points (i + 2)))
      * dist (s.points i) (s.points (i + 1)) :=
  height_eq_sin_mul_aristotle s i

theorem base_eq_dist (s : Affine.Triangle ℝ P) (i : Fin 3) :
    s.base i = dist (s.points (i + 1)) (s.points (i + 2)) := by
  rw [base, volume_eq_dist]
  simp_rw [faceOpposite_point_eq_point_succAbove]
  fin_cases i
  · simp
  · rw [dist_comm]
    simp
  · suffices dist (s.points 0) (s.points (Fin.succAbove 2 1)) = dist (s.points 0) (s.points 1) by
      simpa
    rw [Fin.succAbove_of_castSucc_lt _ _ (by simp)]
    simp


theorem height_eq_sin_mul' (s : Affine.Triangle ℝ P) (i : Fin 3) :
    s.height i = sin (∠ (s.points i) (s.points (i + 1)) (s.points (i + 2))) * s.base (i + 2) := by
  rw [height_eq_sin_mul, base_eq_dist]
  simp_rw [add_assoc]
  simp

theorem height_eq_sin_mul'' (s : Affine.Triangle ℝ P) (i : Fin 3) :
    s.height i = sin (∠ (s.points i) (s.points (i + 2)) (s.points (i + 1))) * s.base (i + 1) := by
  let f := fun (j : Fin 3) ↦ if j = i + 2 then i + 1 else if j = i + 1 then i + 2 else j
  let e : Fin 3 ≃ Fin 3 := {
    toFun := f
    invFun := f
    left_inv := by grind
    right_inv := by grind
  }
  convert height_eq_sin_mul' (s.reindex e) i using 1
  · simp [e, f]
  · congrm sin (∠ ?_ ?_ ?_) * ?_
    · simp [e, f]
    · simp [e, f]
    · simp [e, f]
    · simp_rw [base_eq_dist, add_assoc]
      rw [dist_comm]
      simp [e, f]

theorem volume_eq_height_mul_base₀' (s : Affine.Triangle ℝ P) :
    s.volume = 2⁻¹ * s.height 0 * s.base 0 := by
  rw [volume_eq_height_mul_base₀]
  simp

theorem volume_eq_sin₀₁₂ (s : Affine.Triangle ℝ P) :
    s.volume = 2⁻¹ * sin (∠ (s.points 0) (s.points 1) (s.points 2)) * s.base 0 * s.base 2 := by
  rw [volume_eq_height_mul_base₀', height_eq_sin_mul']
  simp
  ring

theorem volume_eq_height_mul_base₂' (s : Affine.Triangle ℝ P) :
    s.volume = 2⁻¹ * s.height 2 * s.base 2 := by
  rw [height_eq_sin_mul'']
  rw [angle_comm]
  simpa [← mul_assoc] using s.volume_eq_sin₀₁₂

theorem volume_eq_sin₂₀₁ (s : Affine.Triangle ℝ P) :
    s.volume = 2⁻¹ * sin (∠ (s.points 2) (s.points 0) (s.points 1)) * s.base 2 * s.base 1 := by
  rw [volume_eq_height_mul_base₂', height_eq_sin_mul']
  simp
  ring

theorem volume_eq_height_mul_base₁' (s : Affine.Triangle ℝ P) :
    s.volume = 2⁻¹ * s.height 1 * s.base 1 := by
  rw [height_eq_sin_mul'']
  rw [angle_comm]
  simpa [← mul_assoc] using s.volume_eq_sin₂₀₁

theorem volume_eq_height_mul_base (s : Affine.Triangle ℝ P) (i : Fin 3) :
    s.volume = 2⁻¹ * s.height i * s.base i := by
  fin_cases i
  · exact s.volume_eq_height_mul_base₀'
  · exact s.volume_eq_height_mul_base₁'
  · exact s.volume_eq_height_mul_base₂'

theorem excenterWeightsUnnorm_eq (s : Affine.Triangle ℝ P) (signs : Finset (Fin 3))
    (i : Fin 3) :
    s.excenterWeightsUnnorm signs i = 2⁻¹ * s.volume⁻¹ * w[s, signs, i] := by
  obtain h := Simplex.base_pos s i
  rw [s.volume_eq_height_mul_base i]
  by_cases h : i ∈ signs
  <;> simp [excenterWeightsUnnorm, excenterWeightsUnnormBase, h, field]

theorem volume_eq_heron (s : Affine.Triangle ℝ P) :
    s.volume = 4⁻¹ * √((∑ i, w[s, ∅, i]) * (∑ i, w[s, {0}, i])
      * (∑ i, w[s, {1}, i]) * (∑ i, w[s, {2}, i])) := by
  obtain h := s.independent.injective
  obtain h01 := h.ne (show 0 ≠ 1 by simp)
  obtain h12 := h.ne (show 1 ≠ 2 by simp)
  rw [volume_eq_sin₀₁₂]
  convert Theorems100.heron h01 h12.symm using 1
  · simp_rw [base_eq_dist]
    rw [dist_comm]
    simp
    ring
  · rw [show 4⁻¹ = √(16⁻¹) by norm_num]
    rw [← Real.sqrt_mul (by simp)]
    congrm √?_
    trans (2⁻¹ * ∑ i, w[s, ∅, i]) * (2⁻¹ * ∑ i, w[s, {2}, i])
      * (2⁻¹ * ∑ i, w[s, {0}, i]) * (2⁻¹ * ∑ i, w[s, {1}, i])
    · ring
    rw [show dist (s.points 0) (s.points 2) = dist (s.points 2) (s.points 0) by rw [dist_comm]]
    rw [show dist (s.points 2) (s.points 1) = dist (s.points 1) (s.points 2) by rw [dist_comm]]
    congrm ?_ * ?_ * ?_ * ?_
    all_goals
    · simp [Finset.sum, Simplex.excenterWeightsUnnormBase, base_eq_dist]
      ring

theorem wn_pos (s : Affine.Triangle ℝ P) : 0 < ∑ i, w[s, ∅, i] := by
  suffices 0 < base s 0 + (base s 1 + base s 2) by
    simpa [Finset.sum, excenterWeightsUnnormBase]
  positivity

theorem w0_pos (s : Affine.Triangle ℝ P) : 0 < ∑ i, w[s, {0}, i] := by
  suffices 0 < -base s 0 + (base s 1 + base s 2) by
    simpa [Finset.sum, excenterWeightsUnnormBase]
  suffices base s 0 < base s 1 + base s 2 by
    linarith
  suffices dist (s.points 1) (s.points 2) <
      dist (s.points 2) (s.points 0) + dist (s.points 0) (s.points 1) by
    simpa [base_eq_dist]
  rw [dist_comm]
  rw [dist_lt_dist_add_dist_iff]
  obtain h := s.independent
  contrapose! h
  obtain h := h.mem_affineSpan
  contrapose! h
  convert h.notMem_affineSpan_diff 0 {0, 1, 2}
  grind

theorem w1_pos (s : Affine.Triangle ℝ P) : 0 < ∑ i, w[s, {1}, i] := by
  suffices 0 < base s 0 + (-base s 1 + base s 2) by
    simpa [Finset.sum, excenterWeightsUnnormBase]
  suffices base s 1 < base s 0 + base s 2 by
    linarith
  suffices dist (s.points 2) (s.points 0) <
      dist (s.points 1) (s.points 2) + dist (s.points 0) (s.points 1) by
    simpa [base_eq_dist]
  rw [dist_comm, add_comm (dist _ _)]
  rw [dist_lt_dist_add_dist_iff]
  obtain h := s.independent
  contrapose! h
  obtain h := h.mem_affineSpan
  contrapose! h
  convert h.notMem_affineSpan_diff 1 {0, 1, 2}
  grind

theorem w2_pos (s : Affine.Triangle ℝ P) : 0 < ∑ i, w[s, {2}, i] := by
  suffices 0 < base s 0 + (base s 1 - base s 2) by
    simpa [Finset.sum, excenterWeightsUnnormBase]
  suffices base s 2 < base s 0 + base s 1 by
    linarith
  suffices dist (s.points 0) (s.points 1) <
      dist (s.points 1) (s.points 2) + dist (s.points 2) (s.points 0) by
    simpa [base_eq_dist]
  rw [dist_comm]
  rw [dist_lt_dist_add_dist_iff]
  obtain h := s.independent
  contrapose! h
  obtain h := h.mem_affineSpan
  contrapose! h
  convert h.notMem_affineSpan_diff 2 {0, 1, 2}
  grind

theorem sum_excenterWeightsUnnormBase_ne_zero (s : Affine.Triangle ℝ P) (signs : Finset (Fin 3)) :
    ∑ i, w[s, signs, i] ≠ 0 := by
  fin_cases signs
  · exact s.wn_pos.ne.symm
  · exact s.w0_pos.ne.symm
  · exact s.w1_pos.ne.symm
  · obtain h := s.w2_pos.ne.symm
    contrapose! h
    simp [Finset.sum, excenterWeightsUnnormBase] at ⊢ h
    linear_combination -h
  · exact s.w2_pos.ne.symm
  · obtain h := s.w1_pos.ne.symm
    contrapose! h
    simp [Finset.sum, excenterWeightsUnnormBase] at ⊢ h
    linear_combination -h
  · obtain h := s.w0_pos.ne.symm
    contrapose! h
    simp [Finset.sum, excenterWeightsUnnormBase] at ⊢ h
    linear_combination -h
  · obtain h := s.wn_pos.ne.symm
    contrapose! h
    simp [Finset.sum, excenterWeightsUnnormBase] at ⊢ h
    linear_combination -h


theorem volume_eq_exradius_mul (s : Affine.Triangle ℝ P) (signs : Finset (Fin 3)) :
    s.volume = 2⁻¹ * s.exradius signs * |∑ i, w[s, signs, i]| := by
  rw [Simplex.exradius_eq_abs_inv_sum]
  simp_rw [excenterWeightsUnnorm_eq]
  rw [← Finset.mul_sum, mul_inv, mul_inv, abs_mul, abs_inv]
  obtain _ := s.sum_excenterWeightsUnnormBase_ne_zero signs
  rw [abs_of_pos (by simp [s.volume_pos])]
  field

theorem volume_eq_div_circumradius (s : Affine.Triangle ℝ P) :
    s.volume = 4⁻¹ * s.base 0 * s.base 1 * s.base 2 / s.circumradius := by
  rw [s.volume_eq_sin₀₁₂]
  obtain := s.circumradius_pos.ne.symm
  suffices sin (∠ (s.points 0) (s.points 1) (s.points 2)) * 2 * (2 * circumradius s) =
      2 * base s 1 by
    field_simp
    linear_combination this
  rw [← s.dist_div_sin_angle_eq_two_mul_circumradius (show 0 ≠ 1 by simp) (show 0 ≠ 2 by simp)
    (show 1 ≠ 2 by simp)]
  rw [base_eq_dist, dist_comm]
  have : sin (∠ (s.points 0) (s.points 1) (s.points 2)) ≠ 0 := by
    obtain h := s.independent
    contrapose! h
    obtain h := collinear_iff_eq_or_eq_or_sin_eq_zero.mpr (Or.inr (Or.inr h))
    rw [← collinear_iff_not_affineIndependent]
    convert h
    ext i
    suffices (∃ y, s.points y = i) ↔ i = s.points 0 ∨ i = s.points 1 ∨ i = s.points 2 by
      simpa
    constructor
    · intro h
      obtain h | h | h := h <;> grind
    · grind
  simp [field]

theorem excenter_eq_affineCombination' (s : Affine.Triangle ℝ P) (signs : Finset (Fin 3)) :
    s.excenter signs = Finset.affineCombination ℝ Finset.univ s.points
      (w[s, signs, ·] / ∑ i, w[s, signs, i]) := by
  rw [Affine.Simplex.excenter_eq_affineCombination]
  congr
  ext i
  rw [excenterWeights]
  simp only [Nat.reduceAdd, Pi.smul_apply, smul_eq_mul]
  simp_rw [excenterWeightsUnnorm_eq]
  obtain _ := s.sum_excenterWeightsUnnormBase_ne_zero signs
  obtain _ := s.volume_pos.ne.symm
  simp_rw [← Finset.mul_sum]
  field

end Triangle

end Affine
