import Mathlib
import Archive.Wiedijk100Theorems.HeronsFormula


/-
TODO: put this to bib

@misc{scheer2011simplevectorprooffeuerbachs,
      title={A Simple Vector Proof of Feuerbach's Theorem},
      author={Michael Scheer},
      year={2011},
      eprint={1107.1152},
      archivePrefix={arXiv},
      primaryClass={math.MG},
      url={https://arxiv.org/abs/1107.1152},
}

-/

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

theorem nsmul_ninePointCircle_center_vsub_circumcenter {n : ℕ} (s : Simplex ℝ P n) :
    n • (s.ninePointCircle.center -ᵥ s.circumcenter) =
    (n + 1) • (s.centroid -ᵥ s.circumcenter) := by
  by_cases hn : n = 0
  · obtain rfl := hn
    simp [s.circumcenter_eq_point 0, centroid]
  rw [Affine.Simplex.ninePointCircle_center]
  simp_rw [vadd_vsub, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  rw [mul_div_cancel₀ _ (by simpa using hn)]
  norm_cast

theorem ninePointCircle_radius_nonneg {n : ℕ} (s : Simplex ℝ P n) :
    0 ≤ s.ninePointCircle.radius := by
  rw [s.ninePointCircle_radius]
  exact div_nonneg s.circumradius_nonneg (by simp)

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

namespace Simplex


theorem excenterWeightsUnnormBase_sq {n : ℕ} [NeZero n] (s : Simplex ℝ P n)
    (signs : Finset (Fin (n + 1))) (i : Fin (n + 1)) : w[s, signs, i] ^ 2 = s.base i ^ 2 := by
  by_cases hi : i ∈ signs <;> simp [excenterWeightsUnnormBase, hi]

end Simplex

namespace Triangle


theorem height_eq_sin_mul (s : Affine.Triangle ℝ P) (i : Fin 3) :
    s.height i = sin (∠ (s.points i) (s.points (i + 1)) (s.points (i + 2)))
      * dist (s.points i) (s.points (i + 1)) := by
  obtain h := s.independent.injective
  obtain h12 := h.ne (show (i + 1) ≠ (i + 2) by simp)
  rw [height]
  have hmem : s.altitudeFoot i ∈ affineSpan ℝ {s.points (i + 1), s.points (i + 2)} := by
    convert s.altitudeFoot_mem_affineSpan_faceOpposite i
    trans s.points '' {i + 1, i + 2}
    · grind
    rw [range_faceOpposite_points]
    congrm s.points '' ?_
    grind
  by_cases! heq : s.altitudeFoot i = s.points (i + 1)
  · suffices ∠ (s.points i) (s.points (i + 1)) (s.points (i + 2)) = π / 2 by
      simp [heq, this]
    rw [← heq, angle_comm]
    apply angle_orthogonalProjection_self
    simp
  obtain h | h := (collinear_insert_of_mem_affineSpan_pair hmem).wbtw_or_wbtw_or_wbtw
  · have h' : Sbtw ℝ (altitudeFoot s i) (s.points (i + 1)) (s.points (i + 2)) :=
      ⟨h, heq.symm, h12⟩
    have hangle : ∠ (s.points i) (s.points (i + 1)) (s.points (i + 2)) =
        π - ∠ (s.points i) (s.points (i + 1)) (s.altitudeFoot i) := by
      rw [eq_sub_iff_add_eq]
      exact EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi _ h'.angle₃₂₁_eq_pi
    rw [hangle, sin_pi_sub, angle_comm, sin_angle_mul_dist_of_angle_eq_pi_div_two]
    rw [angle_comm]
    apply angle_orthogonalProjection_self
    simp
  · have hangle : ∠ (s.points i) (s.points (i + 1)) (s.points (i + 2)) =
        ∠ (s.points i) (s.points (i + 1)) (s.altitudeFoot i) := by
      obtain h | h := h
      · exact Wbtw.angle_eq_right _ h h12.symm
      · symm
        apply Wbtw.angle_eq_right _ h.symm heq
    rw [hangle, angle_comm, sin_angle_mul_dist_of_angle_eq_pi_div_two]
    rw [angle_comm]
    apply angle_orthogonalProjection_self
    simp

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

theorem w01_neg (s : Affine.Triangle ℝ P) : ∑ i, w[s, {0, 1}, i] < 0 := by
  obtain h := s.w2_pos
  simp [Finset.sum, excenterWeightsUnnormBase] at ⊢ h
  linarith

theorem w12_neg (s : Affine.Triangle ℝ P) : ∑ i, w[s, {1, 2}, i] < 0 := by
  obtain h := s.w0_pos
  simp [Finset.sum, excenterWeightsUnnormBase] at ⊢ h
  linarith

theorem w02_neg (s : Affine.Triangle ℝ P) : ∑ i, w[s, {0, 2}, i] < 0 := by
  obtain h := s.w1_pos
  simp [Finset.sum, excenterWeightsUnnormBase] at ⊢ h
  linarith

theorem w012_neg (s : Affine.Triangle ℝ P) : ∑ i, w[s, {0, 1, 2}, i] < 0 := by
  obtain h := s.wn_pos
  simp [Finset.sum, excenterWeightsUnnormBase] at ⊢ h
  linarith

theorem volume_sq_eq_heron (s : Affine.Triangle ℝ P) :
    s.volume ^ 2 = 16⁻¹ * ((∑ i, w[s, ∅, i]) * (∑ i, w[s, {0}, i])
      * (∑ i, w[s, {1}, i]) * (∑ i, w[s, {2}, i])) := by
  rw [volume_eq_heron, mul_pow, sq_sqrt ?_]
  · ring
  apply le_of_lt
  apply mul_pos (mul_pos (mul_pos s.wn_pos s.w0_pos) s.w1_pos) s.w2_pos

theorem sum_excenterWeightsUnnormBase_ne_zero (s : Affine.Triangle ℝ P) (signs : Finset (Fin 3)) :
    ∑ i, w[s, signs, i] ≠ 0 := by
  fin_cases signs
  · exact s.wn_pos.ne.symm
  · exact s.w0_pos.ne.symm
  · exact s.w1_pos.ne.symm
  · exact s.w01_neg.ne
  · exact s.w2_pos.ne.symm
  · exact s.w02_neg.ne
  · exact s.w12_neg.ne
  · exact s.w012_neg.ne

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

theorem base_mul (s : Affine.Triangle ℝ P) :
    s.base 0 * s.base 1 * s.base 2 = 4 * s.volume * s.circumradius := by
  rw [volume_eq_div_circumradius]
  field [s.circumradius_pos.ne.symm]

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

theorem sum_w (s : Affine.Triangle ℝ P) (signs : Finset (Fin 3)) :
    ∑ i, (w[s, signs, i] / ∑ j, w[s, signs, j]) = 1 := by
  rw [← Finset.sum_div]
  simpa using s.sum_excenterWeightsUnnormBase_ne_zero signs

theorem dist_points_ninePointCircle_center_sq (s : Affine.Triangle ℝ P) (i : Fin 3) :
    dist (s.points i) (s.ninePointCircle.center) ^ 2 =
    4⁻¹ * (s.circumradius ^ 2 - s.base i ^ 2 + s.base (i + 1) ^ 2 + s.base (i + 2) ^ 2) := by
  rw [eq_inv_mul_iff_mul_eq₀ (by simp)]
  calc
    _ = (2 * dist (s.points i) (s.ninePointCircle.center)) ^ 2 := by ring
    _ = (2 * ‖s.points i -ᵥ s.ninePointCircle.center‖) ^ 2 := by rw [dist_eq_norm_vsub]
    _ = (2 * ‖(s.points i -ᵥ s.circumcenter) -
      (s.ninePointCircle.center -ᵥ s.circumcenter)‖) ^ 2 := by simp
    _ = ‖2 • (s.points i -ᵥ s.circumcenter) -
      2 • (s.ninePointCircle.center -ᵥ s.circumcenter)‖ ^ 2 := by
      rw [← smul_sub, RCLike.norm_nsmul ℝ, nsmul_eq_mul]
      norm_cast
    _ = ‖2 • (s.points i -ᵥ s.circumcenter) - 3 • (s.centroid -ᵥ s.circumcenter)‖ ^ 2 := by
      rw [nsmul_ninePointCircle_center_vsub_circumcenter]
    _ = ‖2 • (s.points i -ᵥ s.circumcenter) - ∑ i, (s.points i -ᵥ s.circumcenter)‖ ^ 2 := by
      rw [Affine.Simplex.centroid_vsub_eq]
      rw [← Nat.cast_smul_eq_nsmul ℝ 3, smul_smul]
      norm_num
    _ = ‖(s.points i -ᵥ s.circumcenter) - (s.points (i + 1) -ᵥ s.circumcenter)
        - (s.points (i + 2) -ᵥ s.circumcenter)‖ ^ 2 := by
      congrm ‖?_‖ ^ 2
      fin_cases i
      all_goals
      · simp [Finset.sum, -vsub_sub_vsub_cancel_right]
        module
    _ = dist (s.points i) s.circumcenter ^ 2 + dist (s.points (i + 1)) s.circumcenter ^ 2
      + dist (s.points (i + 2)) s.circumcenter ^ 2
      + 2 * ⟪s.points (i + 1) -ᵥ s.circumcenter, s.points (i + 2) -ᵥ s.circumcenter⟫
      - 2 * ⟪s.points (i + 2) -ᵥ s.circumcenter, s.points i -ᵥ s.circumcenter⟫
      - 2 * ⟪s.points i -ᵥ s.circumcenter, s.points (i + 1) -ᵥ s.circumcenter⟫ := by
      simp_rw [dist_eq_norm_vsub, ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
        real_inner_comm (s.points (i + 2) -ᵥ s.circumcenter) (s.points (i + 1) -ᵥ s.circumcenter),
        real_inner_comm (s.points (i + 1) -ᵥ s.circumcenter) (s.points i -ᵥ s.circumcenter),
        real_inner_comm (s.points i -ᵥ s.circumcenter) (s.points (i + 2) -ᵥ s.circumcenter)]
      ring
    _ = _ := by
      simp_rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
      simp_rw [vsub_sub_vsub_cancel_right]
      simp_rw [← pow_two, ← dist_eq_norm_vsub]
      simp_rw [dist_circumcenter_eq_circumradius]
      simp_rw [base_eq_dist]
      simp_rw [add_assoc]
      simp
      ring

theorem dist_affineCombination_left' {w : Fin 3 → ℝ} (hw : ∑ i, w i = 1) (s : Affine.Triangle ℝ P)
    (q : P) :
    (dist (Finset.affineCombination ℝ Finset.univ s.points w) q) ^ 2 =
    w 0 * dist (s.points 0) q ^ 2 + w 1 * dist (s.points 1) q ^ 2 + w 2 * dist (s.points 2) q ^ 2 -
    (w 1 * w 2 * s.base 0 ^ 2 + w 2 * w 0 * s.base 1 ^ 2 + w 0 * w 1 * s.base 2 ^ 2)
    := by
  simp [dist_affineCombination_left hw, base_eq_dist]

theorem dist_excenter_ninePointCircle_center_sq (s : Affine.Triangle ℝ P) (signs : Finset (Fin 3)) :
    dist (s.excenter signs) s.ninePointCircle.center ^ 2 =
    (s.ninePointCircle.radius -
    s.exradius signs * (|∑ i, w[s, signs, i]| / ∑ i, w[s, signs, i]) * (-1) ^ signs.card) ^ 2 := by
  obtain := s.sum_excenterWeightsUnnormBase_ne_zero signs
  have hsum : w[s, signs, 0] + w[s, signs, 1] + w[s, signs, 2] = ∑ j, w[s, signs, j] := by
    simp [Finset.sum, add_assoc]
  have hprod : (- w[s, signs, 0] + w[s, signs, 1] + w[s, signs, 2]) *
          (w[s, signs, 0] - w[s, signs, 1] + w[s, signs, 2]) *
          (w[s, signs, 0] + w[s, signs, 1] - w[s, signs, 2]) *
          (w[s, signs, 0] + w[s, signs, 1] + w[s, signs, 2]) =
      (∑ i, w[s, ∅, i]) * (∑ i, w[s, {0}, i])
      * (∑ i, w[s, {1}, i]) * (∑ i, w[s, {2}, i]) := by
    fin_cases signs
    all_goals
    · simp [Finset.sum, excenterWeightsUnnormBase]
      ring
  have hmul : w[s, signs, 0] * w[s, signs, 1] * w[s, signs, 2] =
      s.base 0 * s.base 1 * s.base 2 * (-1) ^ signs.card := by
    fin_cases signs
    <;> simp [excenterWeightsUnnormBase, field]
  have hn1 : ((-1 : ℝ) ^ signs.card) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    simp
  calc
    _ = (w[s, signs, 0] / ∑ i, w[s, signs, i]) *
          (4⁻¹ * (circumradius s ^ 2 - base s 0 ^ 2 + base s 1 ^ 2 + base s 2 ^ 2)) +
        (w[s, signs, 1] / ∑ i, w[s, signs, i]) *
          (4⁻¹ * (circumradius s ^ 2 - base s 1 ^ 2 + base s 2 ^ 2 + base s 0 ^ 2)) +
        (w[s, signs, 2] / ∑ i, w[s, signs, i]) *
          (4⁻¹ * (circumradius s ^ 2 - base s 2 ^ 2 + base s 0 ^ 2 + base s 1 ^ 2)) -
        ((w[s, signs, 1] / ∑ i, w[s, signs, i]) * (w[s, signs, 2] / ∑ i, w[s, signs, i])
          * base s 0 ^ 2 +
        (w[s, signs, 2] / ∑ i, w[s, signs, i]) * (w[s, signs, 0] / ∑ i, w[s, signs, i])
          * base s 1 ^ 2 +
        (w[s, signs, 0] / ∑ i, w[s, signs, i]) * (w[s, signs, 1] / ∑ i, w[s, signs, i])
          * base s 2 ^ 2)
       := by
      rw [excenter_eq_affineCombination']
      rw [dist_affineCombination_left' (s.sum_w signs)]
      simp_rw [dist_points_ninePointCircle_center_sq]
      simp
    _ = 4⁻¹ * circumradius s ^ 2 *
          (w[s, signs, 0] + w[s, signs, 1] + w[s, signs, 2]) / ∑ i, w[s, signs, i] +
        4⁻¹ * ((- w[s, signs, 0] + w[s, signs, 1] + w[s, signs, 2]) *
          (w[s, signs, 0] - w[s, signs, 1] + w[s, signs, 2]) *
          (w[s, signs, 0] + w[s, signs, 1] - w[s, signs, 2])
          + 2 * w[s, signs, 0] * w[s, signs, 1] * w[s, signs, 2]) / ∑ i, w[s, signs, i]
        -(w[s, signs, 0] * w[s, signs, 1] * w[s, signs, 2] / (∑ i, w[s, signs, i]) ^ 2)
          * (w[s, signs, 0] + w[s, signs, 1] + w[s, signs, 2]) := by
      simp_rw [← s.excenterWeightsUnnormBase_sq signs]
      field
     _ = 4⁻¹ * circumradius s ^ 2 +
        16⁻¹ * ((- w[s, signs, 0] + w[s, signs, 1] + w[s, signs, 2]) *
          (w[s, signs, 0] - w[s, signs, 1] + w[s, signs, 2]) *
          (w[s, signs, 0] + w[s, signs, 1] - w[s, signs, 2]) *
          (w[s, signs, 0] + w[s, signs, 1] + w[s, signs, 2])) / (4⁻¹ * (∑ i, w[s, signs, i]) ^ 2)
        - 2⁻¹ * (w[s, signs, 0] * w[s, signs, 1] * w[s, signs, 2] / ∑ i, w[s, signs, i])
           := by
      simp_rw [hsum]
      field
    _ = (2⁻¹ * circumradius s) ^ 2 +
      (exradius s signs * |∑ i, w[s, signs, i]| / ∑ i, w[s, signs, i]) ^ 2 *
      ((-1) ^ signs.card) ^ 2 -
      ((exradius s signs * |∑ i, w[s, signs, i]|/ ∑ i, w[s, signs, i])
      * circumradius s * (-1) ^ signs.card ) := by
      rw [hprod, ← volume_sq_eq_heron, hmul, base_mul]
      rw [s.volume_eq_exradius_mul signs, hn1]
      field
    _ = (circumradius s / (2 : ℕ) - exradius s signs *
        (|∑ i, w[s, signs, i]| / ∑ i, w[s, signs, i]) * (-1) ^ signs.card) ^ 2 := by
      field
    _ = _ := by
      rw [← s.ninePointCircle_radius]


theorem dist_excenter_circumcenter (s : Affine.Triangle ℝ P) (signs : Finset (Fin 3)) :
    dist (s.excenter signs) s.circumcenter ^ 2 =
    circumradius s * (s.circumradius - 2 * exradius s signs *
      (-1) ^ signs.card * |∑ i, w[s, signs, i]| / ∑ i, w[s, signs, i]) := by
  obtain := s.sum_excenterWeightsUnnormBase_ne_zero signs
  have hsum : w[s, signs, 0] + w[s, signs, 1] + w[s, signs, 2] = ∑ i, w[s, signs, i] := by
    simp [Finset.sum, add_assoc]
  have hmul : w[s, signs, 0] * w[s, signs, 1] * w[s, signs, 2] =
      s.base 0 * s.base 1 * s.base 2 * (-1) ^ signs.card := by
    fin_cases signs
    <;> simp [excenterWeightsUnnormBase, field]
  calc
    _ =
      (w[s, signs, 0] + w[s, signs, 1] + w[s, signs, 2]) / (∑ i, w[s, signs, i])
      * circumradius s ^ 2 -
      w[s, signs, 0] * w[s, signs, 1] * w[s, signs, 2] / (∑ i, w[s, signs, i]) ^ 2 *
      (w[s, signs, 0] + w[s, signs, 1] + w[s, signs, 2]) := by
      rw [s.excenter_eq_affineCombination']
      rw [dist_affineCombination_left' (s.sum_w signs)]
      simp_rw [dist_circumcenter_eq_circumradius]
      simp_rw [← s.excenterWeightsUnnormBase_sq signs]
      field
    _ = _ := by
      simp_rw [hsum, hmul, base_mul, s.volume_eq_exradius_mul signs]
      field

theorem dist_incenter_circumcenter (s : Affine.Triangle ℝ P) :
    dist s.incenter s.circumcenter ^ 2 = circumradius s * (s.circumradius - 2 * inradius s) := by
  convert s.dist_excenter_circumcenter ∅ using 1
  rw [abs_of_nonneg s.wn_pos.le]
  obtain _ := s.wn_pos.ne.symm
  simp [field]

theorem two_mul_inradius_le_circumradius (s : Affine.Triangle ℝ P) :
    2 * s.inradius ≤ s.circumradius := by
  rw [← sub_nonneg]
  refine nonneg_of_mul_nonneg_right ?_ s.circumradius_pos
  simp [← dist_incenter_circumcenter]

theorem dist_excenter_ninePointCircle_center (s : Affine.Triangle ℝ P)
    (signs : Finset (Fin 3)) (h1 : signs ≠ ∅) (h2 : signs ≠ Finset.univ) :
    dist (s.excenter signs) s.ninePointCircle.center =
    (s.ninePointCircle.radius + s.exradius signs) := by
  rw [← sq_eq_sq₀ (by simp) (add_nonneg (s.ninePointCircle_radius_nonneg)
    (s.exradius_nonneg signs))]
  obtain := s.sum_excenterWeightsUnnormBase_ne_zero signs
  rw [dist_excenter_ninePointCircle_center_sq]
  set d := |∑ i, w[s, signs, i]| / ∑ i, w[s, signs, i]
  fin_cases signs
  · absurd h1
    simp
  · have : d = 1 := by
      unfold d
      rw [abs_of_nonneg ?_]
      · field
      exact s.w0_pos.le
    rw [this]
    simp
  · have : d = 1 := by
      unfold d
      rw [abs_of_nonneg ?_]
      · field
      exact s.w1_pos.le
    rw [this]
    simp
  · have : d = -1 := by
      unfold d
      rw [abs_of_nonpos ?_]
      · field
      exact s.w01_neg.le
    rw [this]
    simp
  · have : d = 1 := by
      unfold d
      rw [abs_of_nonneg ?_]
      · field
      exact s.w2_pos.le
    rw [this]
    simp
  · have : d = -1 := by
      unfold d
      rw [abs_of_nonpos ?_]
      · field
      exact s.w02_neg.le
    rw [this]
    simp
  · have : d = -1 := by
      unfold d
      rw [abs_of_nonpos ?_]
      · field
      exact s.w12_neg.le
    rw [this]
    simp
  · absurd h2
    ext s
    simp
    grind

theorem inradius_le_ninePointCircle_radius (s : Affine.Triangle ℝ P) :
    s.inradius ≤ s.ninePointCircle.radius := by
  rw [ninePointCircle_radius]
  grw [← s.two_mul_inradius_le_circumradius]
  simp

theorem dist_incenter_ninePointCircle_center (s : Affine.Triangle ℝ P) :
    dist (s.incenter) s.ninePointCircle.center  =
    (s.ninePointCircle.radius - s.inradius)  := by
  rw [← sq_eq_sq₀ (by simp) (sub_nonneg.mpr s.inradius_le_ninePointCircle_radius)]
  convert s.dist_excenter_ninePointCircle_center_sq ∅
  obtain := s.sum_excenterWeightsUnnormBase_ne_zero ∅
  rw [abs_of_nonneg s.wn_pos.le]
  rw [inradius, exradius]
  simp [field]

/--
**Feuerbach's Theorem** for excircles
-/
theorem isExtTangent_exsphere_ninePointCircle (s : Affine.Triangle ℝ P)
    (signs : Finset (Fin 3)) (h1 : signs ≠ ∅) (h2 : signs ≠ Finset.univ) :
    (s.exsphere signs).IsExtTangent s.ninePointCircle := by
  rw [Sphere.isExtTangent_iff_dist_center]
  refine ⟨?_, s.exradius_nonneg signs, s.ninePointCircle_radius_nonneg⟩
  obtain h := s.dist_excenter_ninePointCircle_center signs h1 h2
  rw [add_comm] at h
  exact h

/--
**Feuerbach's Theorem** for incircle
-/
theorem isIntTangent_insphere_ninePointCircle (s : Affine.Triangle ℝ P) :
    s.insphere.IsIntTangent s.ninePointCircle := by
  have : Nontrivial V := by
    obtain h := s.independent
    contrapose! h
    rw [affineIndependent_iff_linearIndependent_vsub ℝ _ 0]
    simp_rw [h.eq_zero]
    suffices ∃ (i : Fin 3), i ≠ 0 by simpa
    exact ⟨2, by simp⟩
  rw [Sphere.isIntTangent_iff_dist_center]
  refine ⟨?_, s.exradius_nonneg ∅, s.ninePointCircle_radius_nonneg⟩
  exact s.dist_incenter_ninePointCircle_center

end Triangle

end Affine
