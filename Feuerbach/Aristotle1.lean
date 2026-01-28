/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 939d8115-367c-4206-b621-cf3cb0af3596

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem height_eq_sin_mul (s : Affine.Triangle ℝ P) (i : Fin 3) :
    s.height i = sin (∠ (s.points i) (s.points (i + 1)) (s.points (i + 2)))
      * dist (s.points i) (s.points (i + 1))
-/

import Mathlib


noncomputable section

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

namespace Affine

open Simplex Real EuclideanGeometry

namespace Triangle

noncomputable section AristotleLemmas

/-
The norm of the component of vector u orthogonal to vector v is equal to the norm of u times the sine of the angle between u and v.
-/
theorem norm_sub_proj_eq_norm_mul_sin {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (u v : V) (hv : v ≠ 0) : ‖u - (inner ℝ u v / ‖v‖^2) • v‖ = ‖u‖ * Real.sin (InnerProductGeometry.angle u v) := by
  -- Start by using the Pythagorean identity to rewrite the right-hand side.
  have h_pyth : ‖u‖ * Real.sin (InnerProductGeometry.angle u v) = Real.sqrt (‖u‖^2 * (1 - (inner ℝ u v / (‖u‖ * ‖v‖))^2)) := by
    by_cases hu : u = 0 <;> simp_all +decide [ InnerProductGeometry.angle ];
    exact Real.sin_arccos _;
  rw [ h_pyth, eq_comm, Real.sqrt_eq_iff_mul_self_eq ];
  · have h_norm_sq : ‖u - (inner ℝ u v / ‖v‖ ^ 2) • v‖ ^ 2 = ‖u‖ ^ 2 - 2 * (inner ℝ u v / ‖v‖ ^ 2) * inner ℝ u v + (inner ℝ u v / ‖v‖ ^ 2) ^ 2 * ‖v‖ ^ 2 := by
      rw [ @norm_sub_sq ℝ ] ; norm_num ; ring;
      simp +decide [ inner_smul_right, norm_smul, hv ] ; ring;
      norm_num [ show ‖v‖ ^ 4 = ‖v‖ ^ 2 * ‖v‖ ^ 2 by ring, hv ] ; ring;
      grind;
    by_cases hu : u = 0 <;> simp_all +decide [ mul_pow, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ];
    simp_all +decide [ sq, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( norm_pos_iff.mpr hu ), ne_of_gt ( norm_pos_iff.mpr hv ) ] ; ring;
    simp +decide [ mul_assoc, mul_comm, mul_left_comm, hu ];
  · by_cases hu : u = 0 <;> simp_all +decide [ div_pow, mul_pow ];
    exact div_le_one_of_le₀ ( by nlinarith only [ abs_le.mp ( abs_real_inner_le_norm u v ) ] ) ( by positivity );
  · positivity

/-
The distance from a point p to the line spanned by a 1-simplex (segment) is equal to the distance from p to one vertex multiplied by the sine of the angle between the vector to p and the vector to the other vertex.
-/
theorem dist_simplex_1_projection_eq {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] (s : Affine.Simplex ℝ P 1) (p : P) : dist p (s.orthogonalProjectionSpan p) = dist p (s.points 0) * Real.sin (EuclideanGeometry.angle p (s.points 0) (s.points 1)) := by
  convert norm_sub_proj_eq_norm_mul_sin ( p -ᵥ s.points 0 ) ( s.points 1 -ᵥ s.points 0 ) _ using 1;
  · convert dist_eq_norm_vsub V p _ using 2;
    simp +decide [ Affine.Simplex.orthogonalProjectionSpan ];
    -- By definition of orthogonal projection, we know that the vector from p to its orthogonal projection onto the line is orthogonal to the line's direction vector.
    have h_orthogonal : (p -ᵥ (EuclideanGeometry.orthogonalProjection (affineSpan ℝ (Set.range s.points)) p)) ∈ (Submodule.span ℝ {s.points 1 -ᵥ s.points 0})ᗮ := by
      have h_orthogonal : (p -ᵥ (EuclideanGeometry.orthogonalProjection (affineSpan ℝ (Set.range s.points)) p)) ∈ (affineSpan ℝ (Set.range s.points)).directionᗮ := by
        exact
          vsub_orthogonalProjection_mem_direction_orthogonal (affineSpan ℝ (Set.range s.points)) p;
      convert h_orthogonal using 1;
      rw [ direction_affineSpan ];
      rw [ vectorSpan_eq_span_vsub_set_right ];
      rotate_left;
      exact s.points 0;
      · exact Set.mem_range_self _;
      · congr! 1;
        refine' le_antisymm _ _ <;> norm_num [ Submodule.span_le, Set.image_subset_iff ];
        · exact Submodule.subset_span ⟨ s.points 1, Set.mem_range_self _, rfl ⟩;
        · rintro _ ⟨ i, rfl ⟩ ; fin_cases i <;> simp +decide [ Submodule.mem_span_singleton ] ;
    -- By definition of orthogonal projection, we know that the vector from p to its orthogonal projection onto the line is orthogonal to the line's direction vector. Therefore, we can write:
    have h_orthogonal : ∃ c : ℝ, p -ᵥ (EuclideanGeometry.orthogonalProjection (affineSpan ℝ (Set.range s.points)) p) = c • (s.points 1 -ᵥ s.points 0) + (p -ᵥ s.points 0) - (inner ℝ (p -ᵥ s.points 0) (s.points 1 -ᵥ s.points 0) / ‖s.points 1 -ᵥ s.points 0‖^2) • (s.points 1 -ᵥ s.points 0) := by
      have h_orthogonal : ∃ c : ℝ, (p -ᵥ (EuclideanGeometry.orthogonalProjection (affineSpan ℝ (Set.range s.points)) p)) - (p -ᵥ s.points 0) + (inner ℝ (p -ᵥ s.points 0) (s.points 1 -ᵥ s.points 0) / ‖s.points 1 -ᵥ s.points 0‖^2) • (s.points 1 -ᵥ s.points 0) = c • (s.points 1 -ᵥ s.points 0) := by
        have h_orthogonal : (p -ᵥ (EuclideanGeometry.orthogonalProjection (affineSpan ℝ (Set.range s.points)) p)) - (p -ᵥ s.points 0) + (inner ℝ (p -ᵥ s.points 0) (s.points 1 -ᵥ s.points 0) / ‖s.points 1 -ᵥ s.points 0‖^2) • (s.points 1 -ᵥ s.points 0) ∈ (Submodule.span ℝ {s.points 1 -ᵥ s.points 0})ᗮᗮ := by
          simp_all +decide [ Submodule.mem_orthogonal' ];
          rw [ Submodule.mem_span_singleton ];
          have h_orthogonal : (s.points 0 -ᵥ (EuclideanGeometry.orthogonalProjection (affineSpan ℝ (Set.range s.points)) p)) + (inner ℝ (p -ᵥ s.points 0) (s.points 1 -ᵥ s.points 0) / ‖s.points 1 -ᵥ s.points 0‖^2) • (s.points 1 -ᵥ s.points 0) ∈ (Submodule.span ℝ {s.points 1 -ᵥ s.points 0}) := by
            have h_orthogonal : (s.points 0 -ᵥ (EuclideanGeometry.orthogonalProjection (affineSpan ℝ (Set.range s.points)) p)) ∈ (Submodule.span ℝ {s.points 1 -ᵥ s.points 0}) := by
              have h_orthogonal : (s.points 0 -ᵥ (EuclideanGeometry.orthogonalProjection (affineSpan ℝ (Set.range s.points)) p)) ∈ (affineSpan ℝ (Set.range s.points)).direction := by
                exact AffineSubspace.vsub_mem_direction ( show s.points 0 ∈ affineSpan ℝ ( Set.range s.points ) from mem_affineSpan ℝ ( Set.mem_range_self 0 ) ) ( EuclideanGeometry.orthogonalProjection_mem p );
              convert h_orthogonal using 1;
              rw [ direction_affineSpan ];
              rw [ vectorSpan_eq_span_vsub_set_right ];
              rotate_left;
              exact s.points 0;
              · exact Set.mem_range_self _;
              · refine' le_antisymm _ _ <;> simp +decide [ Submodule.span_le, Set.subset_def ];
                · exact Submodule.subset_span ⟨ s.points 1, Set.mem_range_self _, rfl ⟩;
                · rintro a ( rfl | rfl ) <;> simp +decide [ Submodule.mem_span_singleton ];
            exact Submodule.add_mem _ h_orthogonal ( Submodule.smul_mem _ _ ( Submodule.subset_span ( Set.mem_singleton _ ) ) );
          rw [ Submodule.mem_span_singleton ] at h_orthogonal ; tauto;
        rw [ Submodule.orthogonal_orthogonal ] at h_orthogonal;
        rw [ Submodule.mem_span_singleton ] at h_orthogonal ; tauto;
      exact ⟨ h_orthogonal.choose, by rw [ ← h_orthogonal.choose_spec ] ; abel1 ⟩;
    obtain ⟨ c, hc ⟩ := h_orthogonal;
    have := h_orthogonal ( s.points 1 -ᵥ s.points 0 ) ( Submodule.mem_span_singleton_self _ ) ; simp_all +decide [ inner_add_left, inner_smul_left ] ;
    simp_all +decide [ inner_add_right, inner_sub_right, inner_smul_right ];
    simp_all +decide [ real_inner_comm, real_inner_self_eq_norm_sq ];
    by_cases h : ‖s.points 1 -ᵥ s.points 0‖ = 0 <;> simp_all +decide [ sub_eq_iff_eq_add ];
  · simp +decide [ EuclideanGeometry.angle, dist_eq_norm_vsub ];
  · exact vsub_ne_zero.mpr ( s.independent.injective.ne ( by decide ) )

end AristotleLemmas

theorem height_eq_sin_mul_aristotle (s : Affine.Triangle ℝ P) (i : Fin 3) :
    s.height i = sin (∠ (s.points i) (s.points (i + 1)) (s.points (i + 2)))
      * dist (s.points i) (s.points (i + 1)) := by
  -- By definition of height, we know that it is equal to the distance from the i-th point to the line formed by the other two points in the triangle.
  have h_height_def : s.height i = dist (s.points i) (Affine.Simplex.orthogonalProjectionSpan (Affine.Simplex.faceOpposite s i) (s.points i)) := by
    exact ext_cauchy rfl;
  -- By definition of orthogonal projection, we know that the distance from a point to the line formed by the other two points in the triangle is equal to the height of the triangle.
  have h_proj : dist (s.points i) (Affine.Simplex.orthogonalProjectionSpan (Affine.Simplex.faceOpposite s i) (s.points i)) = dist (s.points i) (Affine.Simplex.points (Affine.Simplex.faceOpposite s i) 0) * Real.sin (EuclideanGeometry.angle (s.points i) (Affine.Simplex.points (Affine.Simplex.faceOpposite s i) 0) (Affine.Simplex.points (Affine.Simplex.faceOpposite s i) 1)) := by
    convert dist_simplex_1_projection_eq ( Affine.Simplex.faceOpposite s i ) ( s.points i ) using 1;
  fin_cases i <;> simp_all +decide [ Fin.add_def, EuclideanGeometry.angle ];
  · simp_all +decide [ mul_comm, Affine.Simplex.faceOpposite ];
    simp +decide [ Affine.Simplex.face ];
  · simp +decide [ Affine.Simplex.faceOpposite, mul_comm ];
    simp +decide [ Affine.Simplex.face, Fin.forall_fin_succ ];
    simp +decide [ dist_eq_norm_vsub, InnerProductGeometry.angle ];
    rw [ Real.sin_arccos, Real.sin_arccos ];
    by_cases h : s.points 1 -ᵥ s.points 0 = 0 <;> by_cases h' : s.points 2 -ᵥ s.points 0 = 0 <;> simp_all +decide [ norm_sub_rev, inner_sub_left, inner_sub_right ];
    · exact absurd h ( s.independent.injective.ne ( by decide ) );
    · by_cases h'' : s.points 1 -ᵥ s.points 2 = 0 <;> simp_all +decide [ norm_sub_rev, inner_sub_left, inner_sub_right ];
      · have := s.independent.injective.ne ( show 1 ≠ 2 by decide ) ; aesop;
      · simp +decide [ norm_sub_rev, inner_sub_left, inner_sub_right, div_pow, mul_pow, mul_assoc, mul_comm, mul_left_comm, h, h', h'' ];
        rw [ one_sub_div, one_sub_div ] <;> norm_num [ h, h', h'', norm_ne_zero_iff, sub_eq_zero ];
        · rw [ mul_div, mul_div, div_eq_div_iff ];
          · rw [ show s.points 1 -ᵥ s.points 2 = ( s.points 1 -ᵥ s.points 0 ) - ( s.points 2 -ᵥ s.points 0 ) by rw [ vsub_sub_vsub_cancel_right ] ] ; rw [ inner_sub_left ] ; ring;
            rw [ show s.points 0 -ᵥ s.points 2 = - ( s.points 2 -ᵥ s.points 0 ) by rw [ neg_vsub_eq_vsub_rev ], inner_neg_right, inner_neg_right ] ; ring;
            norm_num [ norm_sub_sq_real, inner_self_eq_norm_sq_to_K ] ; ring;
            rw [ show s.points 1 -ᵥ s.points 2 = ( s.points 1 -ᵥ s.points 0 ) - ( s.points 2 -ᵥ s.points 0 ) by rw [ vsub_sub_vsub_cancel_right ] ] ; rw [ norm_sub_sq_real ] ; ring;
            rw [ show s.points 0 -ᵥ s.points 2 = - ( s.points 2 -ᵥ s.points 0 ) by rw [ neg_vsub_eq_vsub_rev ], norm_neg ] ; ring;
          · exact mul_ne_zero ( norm_ne_zero_iff.mpr ( vsub_ne_zero.mpr h ) ) ( norm_ne_zero_iff.mpr ( vsub_ne_zero.mpr h' ) );
          · simp +decide [ sub_eq_zero, h, h', h'' ];
            tauto;
        · tauto;
  · simp_all +decide [ Affine.Simplex.faceOpposite ];
    simp +decide [ mul_comm, Affine.Simplex.face ];
    exact Or.inl rfl

end Triangle

end Affine
