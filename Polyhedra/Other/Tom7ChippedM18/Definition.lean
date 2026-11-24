import Definitions.Polyhedra

/-!
# The Chipped M18 of Tom 7

The polyhedron `Other.Tom7ChippedM18.polyhedron`: the convex hull of 19 points.
-/

namespace Nieuwland.Other.Tom7ChippedM18

open Classical in
/-- The Chipped M18 of Tom 7: the convex hull of these 19 points. -/
noncomputable def polyhedron : Polyhedron where
  vertices := [
    ![-107/192, 13/48, 13/48],
    ![-209/384, 101/384, 9/32],
    ![-209/384, 9/32, 101/384],
    ![-249/704, 39/176, 127/352],
    ![-249/704, 127/352, 39/176],
    ![-9/32, -9/32, -9/32],
    ![3/32, 3/32, 17/32],
    ![3/32, 17/32, 3/32],
    ![39/176, -249/704, 127/352],
    ![39/176, 127/352, -249/704],
    ![101/384, -209/384, 9/32],
    ![101/384, 9/32, -209/384],
    ![13/48, -107/192, 13/48],
    ![13/48, 13/48, -107/192],
    ![9/32, -209/384, 101/384],
    ![9/32, 101/384, -209/384],
    ![127/352, -249/704, 39/176],
    ![127/352, 39/176, -249/704],
    ![17/32, 3/32, 3/32]].toFinset

end Nieuwland.Other.Tom7ChippedM18
