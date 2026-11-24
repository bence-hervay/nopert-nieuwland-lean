import Modules.Pose.Optimum
import Polyhedra.Other.Tom7ChippedM18.Proof.Certificate
import Polyhedra.Other.Tom7ChippedM18.Proof.FullDim

/-!
# The Chipped M18 of Tom 7: a Nopert

The certificate's theorem under the reader's names, and the Nieuwland number `1`.
-/

namespace Nieuwland.Other.Tom7ChippedM18.Proof

open Notation

theorem fullDim : polyhedron.FullDim :=
  Polyhedra.externalTom7ChippedM18_fullDim

theorem isNopert : polyhedron.IsNopert :=
  Polyhedra.externalTom7ChippedM18_not_isRupert

theorem nieuwland_eq_one : ν polyhedron = 1 :=
  Polyhedron.nieuwland_eq_one_of_isNopert fullDim isNopert

end Nieuwland.Other.Tom7ChippedM18.Proof
