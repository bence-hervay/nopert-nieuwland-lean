import Polyhedra.Other.Tom7ChippedM18.Definition
import Modules.Check.Leaf.FullDim

/-!
# The fixture `external/tom7/chipped-m18` is full-dimensional

The points of `Other.Tom7ChippedM18.polyhedron` times `4224` as exact values in `ℤ`, exported by
`code/lean-export dim`: three of their differences are linearly independent (`spanOk`, checked by
the kernel), so their polyhedron is full-dimensional (`Polyhedron.fullDim_of_spanOk`), and scaled
back (`eq_smul`, `Polyhedron.FullDim.smul`), so is `Other.Tom7ChippedM18.polyhedron`.
-/

namespace Nieuwland.Polyhedra.ExternalTom7ChippedM18Dim

open Check

/-- The points of `Other.Tom7ChippedM18.polyhedron` times `4224`. -/
def points : List (V3 ℤ) := [
    ⟨-2354, 1144, 1144⟩,
    ⟨-2299, 1111, 1188⟩,
    ⟨-2299, 1188, 1111⟩,
    ⟨-1494, 936, 1524⟩,
    ⟨-1494, 1524, 936⟩,
    ⟨-1188, -1188, -1188⟩,
    ⟨396, 396, 2244⟩,
    ⟨396, 2244, 396⟩,
    ⟨936, -1494, 1524⟩,
    ⟨936, 1524, -1494⟩,
    ⟨1111, -2299, 1188⟩,
    ⟨1111, 1188, -2299⟩,
    ⟨1144, -2354, 1144⟩,
    ⟨1144, 1144, -2354⟩,
    ⟨1188, -2299, 1111⟩,
    ⟨1188, 1111, -2299⟩,
    ⟨1524, -1494, 936⟩,
    ⟨1524, 936, -1494⟩,
    ⟨2244, 396, 396⟩]

theorem span_ok : spanOk points 0 1 2 5 = true := by
  decide +kernel

/-! The points, scaled back, are the fixture's. -/

theorem pt0 : (1 / 4224 : ℝ) • Exact.reV (⟨-2354, 1144, 1144⟩ : V3 ℤ) = ![-107/192, 13/48,
    13/48] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt1 : (1 / 4224 : ℝ) • Exact.reV (⟨-2299, 1111, 1188⟩ : V3 ℤ) = ![-209/384, 101/384,
    9/32] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt2 : (1 / 4224 : ℝ) • Exact.reV (⟨-2299, 1188, 1111⟩ : V3 ℤ) = ![-209/384, 9/32,
    101/384] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt3 : (1 / 4224 : ℝ) • Exact.reV (⟨-1494, 936, 1524⟩ : V3 ℤ) = ![-249/704, 39/176,
    127/352] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt4 : (1 / 4224 : ℝ) • Exact.reV (⟨-1494, 1524, 936⟩ : V3 ℤ) = ![-249/704, 127/352,
    39/176] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt5 : (1 / 4224 : ℝ) • Exact.reV (⟨-1188, -1188, -1188⟩ : V3 ℤ) = ![-9/32, -9/32, -9/32]
    := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt6 : (1 / 4224 : ℝ) • Exact.reV (⟨396, 396, 2244⟩ : V3 ℤ) = ![3/32, 3/32, 17/32] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt7 : (1 / 4224 : ℝ) • Exact.reV (⟨396, 2244, 396⟩ : V3 ℤ) = ![3/32, 17/32, 3/32] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt8 : (1 / 4224 : ℝ) • Exact.reV (⟨936, -1494, 1524⟩ : V3 ℤ) = ![39/176, -249/704,
    127/352] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt9 : (1 / 4224 : ℝ) • Exact.reV (⟨936, 1524, -1494⟩ : V3 ℤ) = ![39/176, 127/352,
    -249/704] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt10 : (1 / 4224 : ℝ) • Exact.reV (⟨1111, -2299, 1188⟩ : V3 ℤ) = ![101/384, -209/384,
    9/32] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt11 : (1 / 4224 : ℝ) • Exact.reV (⟨1111, 1188, -2299⟩ : V3 ℤ) = ![101/384, 9/32,
    -209/384] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt12 : (1 / 4224 : ℝ) • Exact.reV (⟨1144, -2354, 1144⟩ : V3 ℤ) = ![13/48, -107/192,
    13/48] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt13 : (1 / 4224 : ℝ) • Exact.reV (⟨1144, 1144, -2354⟩ : V3 ℤ) = ![13/48, 13/48,
    -107/192] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt14 : (1 / 4224 : ℝ) • Exact.reV (⟨1188, -2299, 1111⟩ : V3 ℤ) = ![9/32, -209/384,
    101/384] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt15 : (1 / 4224 : ℝ) • Exact.reV (⟨1188, 1111, -2299⟩ : V3 ℤ) = ![9/32, 101/384,
    -209/384] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt16 : (1 / 4224 : ℝ) • Exact.reV (⟨1524, -1494, 936⟩ : V3 ℤ) = ![127/352, -249/704,
    39/176] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt17 : (1 / 4224 : ℝ) • Exact.reV (⟨1524, 936, -1494⟩ : V3 ℤ) = ![127/352, 39/176,
    -249/704] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem pt18 : (1 / 4224 : ℝ) • Exact.reV (⟨2244, 396, 396⟩ : V3 ℤ) = ![17/32, 3/32, 3/32] := by
  refine Exact.smul_reV_eq ?_ ?_ ?_ <;> push_cast [Exact.re_int] <;> ring

theorem eq_smul : Other.Tom7ChippedM18.polyhedron = (Polyhedron.ofPoints points).smul (1 / 4224) := by
  refine Polyhedron.eq_smul_ofPoints rfl ?_
  simp only [points, List.map_cons, List.map_nil, pt0, pt1, pt2, pt3, pt4, pt5, pt6, pt7, pt8,
    pt9, pt10, pt11, pt12, pt13, pt14, pt15, pt16, pt17, pt18]

end Nieuwland.Polyhedra.ExternalTom7ChippedM18Dim

namespace Nieuwland.Polyhedra

/-- **The fixture `external/tom7/chipped-m18` is full-dimensional.** -/
theorem externalTom7ChippedM18_fullDim : Other.Tom7ChippedM18.polyhedron.FullDim := by
  rw [ExternalTom7ChippedM18Dim.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk ExternalTom7ChippedM18Dim.span_ok).smul (by norm_num)

end Nieuwland.Polyhedra
