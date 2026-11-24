import Polyhedra.Other.Tom7ChippedM18.Proof.Points
import Polyhedra.Other.Tom7ChippedM18.Certificates.Chunk0
import Polyhedra.Other.Tom7ChippedM18.Certificates.Chunk1
import Polyhedra.Other.Tom7ChippedM18.Certificates.Chunk2
import Polyhedra.Other.Tom7ChippedM18.Certificates.Chunk3
import Polyhedra.Other.Tom7ChippedM18.Certificates.Chunk4
import Polyhedra.Other.Tom7ChippedM18.Certificates.Chunk5
import Polyhedra.Other.Tom7ChippedM18.Certificates.Chunk6
import Polyhedra.Other.Tom7ChippedM18.Certificates.Chunk7
import Polyhedra.Other.Tom7ChippedM18.Certificates.Chunk8
import Polyhedra.Other.Tom7ChippedM18.Certificates.Chunk9
import Polyhedra.Other.Tom7ChippedM18.Certificates.Chunk10
import Polyhedra.Other.Tom7ChippedM18.Certificates.Chunk11
import Polyhedra.Other.Tom7ChippedM18.Certificates.Chunk12
import Modules.Certificate.Whole
import Modules.Check.Leaf.FullDim
import Modules.Nieuwland.Basic
import Modules.System.SystemRoot
import Modules.System.Readable
import Modules.System.Single

set_option linter.style.longLine false

/-!
# Exported nodes

Nodes of the cover of
`gs://main-69696-data/noperts-results/chipped-2026-11-24/chipped-m18/certificate.jsonl`, assembled
from 13 chunks: 133867 items, 133867 of them checked (129027 checks); unsupported: none. Generated
by `code/lean-export`. The nodes: `Node0`: root 0, path ``; `Node1`: root 1, path ``; `Node2`: root
2, path ``; `Node3`: root 3, path ``; `Node4`: root 4, path ``; `Node5`: root 5, path ``; `Node6`:
root 6, path ``; `Node7`: root 7, path ``; `Node8`: root 8, path ``; `Node9`: root 9, path ``;
`Node10`: root 10, path ``; `Node11`: root 11, path ``.
-/

open Nieuwland.Check Nieuwland.Cert

/-!
## Node 0

The node at path `` of root 0: 10399 items in 1 chunk, 10399 of them checked (9848 checks);
unsupported: none.
-/

namespace Nieuwland.Results.Gen.ExternalTom7ChippedM18.Node0

/-- The box of the node. -/
def box : ChartBox :=
  ⟨0, 0, ⟨[-1, -1, -1, -1, -1], [1, 1, 1, 1, 1], 1⟩⟩

/-- The chunks: their boxes and unsupported parts. -/
def chunks : Cover (ChartBox × List (Unsupported ℤ)) :=
  (.leaf (Chunk0.box, Chunk0.missing))

theorem chunks_check : chunks.check (fun B c ↦ B.subset c.1) box = true := by
  decide +kernel

/-- The unsupported parts of all chunks. -/
def missing : List (Unsupported ℤ) :=
  chunks.data.flatMap Prod.snd

theorem missing_length : missing.length = 0 := by
  decide +kernel

/-- **The node.** Every pose of its box is settled, if the unsupported parts are. -/
theorem settled (hM : ∀ u ∈ missing, ∀ p ∈ u.region.poses,
    SettledRot points symm (Exact.rePre u.pre) p) :
    ∀ p ∈ box.poses, Settled points symm p :=
  Cover.settled_of_chunks (T := chunks)
    Chunk0.settled hM chunks_check

/-- **The node, unconditionally:** it has no unsupported parts. -/
theorem settled_all : ∀ p ∈ box.poses, Settled points symm p :=
  settled fun u hu ↦ by
    rw [List.length_eq_zero_iff.mp missing_length] at hu
    simp at hu

end Nieuwland.Results.Gen.ExternalTom7ChippedM18.Node0

/-!
## Node 1

The node at path `` of root 1: 3359 items in 1 chunk, 3359 of them checked (3359 checks);
unsupported: none.
-/

namespace Nieuwland.Results.Gen.ExternalTom7ChippedM18.Node1

/-- The box of the node. -/
def box : ChartBox :=
  ⟨0, 1, ⟨[-1, -1, -1, -1, -1], [1, 1, 1, 1, 1], 1⟩⟩

/-- The chunks: their boxes and unsupported parts. -/
def chunks : Cover (ChartBox × List (Unsupported ℤ)) :=
  (.leaf (Chunk1.box, Chunk1.missing))

theorem chunks_check : chunks.check (fun B c ↦ B.subset c.1) box = true := by
  decide +kernel

/-- The unsupported parts of all chunks. -/
def missing : List (Unsupported ℤ) :=
  chunks.data.flatMap Prod.snd

theorem missing_length : missing.length = 0 := by
  decide +kernel

/-- **The node.** Every pose of its box is settled, if the unsupported parts are. -/
theorem settled (hM : ∀ u ∈ missing, ∀ p ∈ u.region.poses,
    SettledRot points symm (Exact.rePre u.pre) p) :
    ∀ p ∈ box.poses, Settled points symm p :=
  Cover.settled_of_chunks (T := chunks)
    Chunk1.settled hM chunks_check

/-- **The node, unconditionally:** it has no unsupported parts. -/
theorem settled_all : ∀ p ∈ box.poses, Settled points symm p :=
  settled fun u hu ↦ by
    rw [List.length_eq_zero_iff.mp missing_length] at hu
    simp at hu

end Nieuwland.Results.Gen.ExternalTom7ChippedM18.Node1

/-!
## Node 2

The node at path `` of root 2: 3789 items in 1 chunk, 3789 of them checked (3789 checks);
unsupported: none.
-/

namespace Nieuwland.Results.Gen.ExternalTom7ChippedM18.Node2

/-- The box of the node. -/
def box : ChartBox :=
  ⟨0, 2, ⟨[-1, -1, -1, -1, -1], [1, 1, 1, 1, 1], 1⟩⟩

/-- The chunks: their boxes and unsupported parts. -/
def chunks : Cover (ChartBox × List (Unsupported ℤ)) :=
  (.leaf (Chunk2.box, Chunk2.missing))

theorem chunks_check : chunks.check (fun B c ↦ B.subset c.1) box = true := by
  decide +kernel

/-- The unsupported parts of all chunks. -/
def missing : List (Unsupported ℤ) :=
  chunks.data.flatMap Prod.snd

theorem missing_length : missing.length = 0 := by
  decide +kernel

/-- **The node.** Every pose of its box is settled, if the unsupported parts are. -/
theorem settled (hM : ∀ u ∈ missing, ∀ p ∈ u.region.poses,
    SettledRot points symm (Exact.rePre u.pre) p) :
    ∀ p ∈ box.poses, Settled points symm p :=
  Cover.settled_of_chunks (T := chunks)
    Chunk2.settled hM chunks_check

/-- **The node, unconditionally:** it has no unsupported parts. -/
theorem settled_all : ∀ p ∈ box.poses, Settled points symm p :=
  settled fun u hu ↦ by
    rw [List.length_eq_zero_iff.mp missing_length] at hu
    simp at hu

end Nieuwland.Results.Gen.ExternalTom7ChippedM18.Node2

/-!
## Node 3

The node at path `` of root 3: 3724 items in 1 chunk, 3724 of them checked (3724 checks);
unsupported: none.
-/

namespace Nieuwland.Results.Gen.ExternalTom7ChippedM18.Node3

/-- The box of the node. -/
def box : ChartBox :=
  ⟨0, 3, ⟨[-1, -1, -1, -1, -1], [1, 1, 1, 1, 1], 1⟩⟩

/-- The chunks: their boxes and unsupported parts. -/
def chunks : Cover (ChartBox × List (Unsupported ℤ)) :=
  (.leaf (Chunk3.box, Chunk3.missing))

theorem chunks_check : chunks.check (fun B c ↦ B.subset c.1) box = true := by
  decide +kernel

/-- The unsupported parts of all chunks. -/
def missing : List (Unsupported ℤ) :=
  chunks.data.flatMap Prod.snd

theorem missing_length : missing.length = 0 := by
  decide +kernel

/-- **The node.** Every pose of its box is settled, if the unsupported parts are. -/
theorem settled (hM : ∀ u ∈ missing, ∀ p ∈ u.region.poses,
    SettledRot points symm (Exact.rePre u.pre) p) :
    ∀ p ∈ box.poses, Settled points symm p :=
  Cover.settled_of_chunks (T := chunks)
    Chunk3.settled hM chunks_check

/-- **The node, unconditionally:** it has no unsupported parts. -/
theorem settled_all : ∀ p ∈ box.poses, Settled points symm p :=
  settled fun u hu ↦ by
    rw [List.length_eq_zero_iff.mp missing_length] at hu
    simp at hu

end Nieuwland.Results.Gen.ExternalTom7ChippedM18.Node3

/-!
## Node 4

The node at path `` of root 4: 6832 items in 1 chunk, 6832 of them checked (6579 checks);
unsupported: none.
-/

namespace Nieuwland.Results.Gen.ExternalTom7ChippedM18.Node4

/-- The box of the node. -/
def box : ChartBox :=
  ⟨1, 0, ⟨[-1, -1, -1, -1, -1], [1, 1, 1, 1, 1], 1⟩⟩

/-- The chunks: their boxes and unsupported parts. -/
def chunks : Cover (ChartBox × List (Unsupported ℤ)) :=
  (.leaf (Chunk4.box, Chunk4.missing))

theorem chunks_check : chunks.check (fun B c ↦ B.subset c.1) box = true := by
  decide +kernel

/-- The unsupported parts of all chunks. -/
def missing : List (Unsupported ℤ) :=
  chunks.data.flatMap Prod.snd

theorem missing_length : missing.length = 0 := by
  decide +kernel

/-- **The node.** Every pose of its box is settled, if the unsupported parts are. -/
theorem settled (hM : ∀ u ∈ missing, ∀ p ∈ u.region.poses,
    SettledRot points symm (Exact.rePre u.pre) p) :
    ∀ p ∈ box.poses, Settled points symm p :=
  Cover.settled_of_chunks (T := chunks)
    Chunk4.settled hM chunks_check

/-- **The node, unconditionally:** it has no unsupported parts. -/
theorem settled_all : ∀ p ∈ box.poses, Settled points symm p :=
  settled fun u hu ↦ by
    rw [List.length_eq_zero_iff.mp missing_length] at hu
    simp at hu

end Nieuwland.Results.Gen.ExternalTom7ChippedM18.Node4

/-!
## Node 5

The node at path `` of root 5: 861 items in 1 chunk, 861 of them checked (861 checks); unsupported:
none.
-/

namespace Nieuwland.Results.Gen.ExternalTom7ChippedM18.Node5

/-- The box of the node. -/
def box : ChartBox :=
  ⟨1, 1, ⟨[-1, -1, -1, -1, -1], [1, 1, 1, 1, 1], 1⟩⟩

/-- The chunks: their boxes and unsupported parts. -/
def chunks : Cover (ChartBox × List (Unsupported ℤ)) :=
  (.leaf (Chunk5.box, Chunk5.missing))

theorem chunks_check : chunks.check (fun B c ↦ B.subset c.1) box = true := by
  decide +kernel

/-- The unsupported parts of all chunks. -/
def missing : List (Unsupported ℤ) :=
  chunks.data.flatMap Prod.snd

theorem missing_length : missing.length = 0 := by
  decide +kernel

/-- **The node.** Every pose of its box is settled, if the unsupported parts are. -/
theorem settled (hM : ∀ u ∈ missing, ∀ p ∈ u.region.poses,
    SettledRot points symm (Exact.rePre u.pre) p) :
    ∀ p ∈ box.poses, Settled points symm p :=
  Cover.settled_of_chunks (T := chunks)
    Chunk5.settled hM chunks_check

/-- **The node, unconditionally:** it has no unsupported parts. -/
theorem settled_all : ∀ p ∈ box.poses, Settled points symm p :=
  settled fun u hu ↦ by
    rw [List.length_eq_zero_iff.mp missing_length] at hu
    simp at hu

end Nieuwland.Results.Gen.ExternalTom7ChippedM18.Node5

/-!
## Node 6

The node at path `` of root 6: 1328 items in 1 chunk, 1328 of them checked (1328 checks);
unsupported: none.
-/

namespace Nieuwland.Results.Gen.ExternalTom7ChippedM18.Node6

/-- The box of the node. -/
def box : ChartBox :=
  ⟨1, 2, ⟨[-1, -1, -1, -1, -1], [1, 1, 1, 1, 1], 1⟩⟩

/-- The chunks: their boxes and unsupported parts. -/
def chunks : Cover (ChartBox × List (Unsupported ℤ)) :=
  (.leaf (Chunk6.box, Chunk6.missing))

theorem chunks_check : chunks.check (fun B c ↦ B.subset c.1) box = true := by
  decide +kernel

/-- The unsupported parts of all chunks. -/
def missing : List (Unsupported ℤ) :=
  chunks.data.flatMap Prod.snd

theorem missing_length : missing.length = 0 := by
  decide +kernel

/-- **The node.** Every pose of its box is settled, if the unsupported parts are. -/
theorem settled (hM : ∀ u ∈ missing, ∀ p ∈ u.region.poses,
    SettledRot points symm (Exact.rePre u.pre) p) :
    ∀ p ∈ box.poses, Settled points symm p :=
  Cover.settled_of_chunks (T := chunks)
    Chunk6.settled hM chunks_check

/-- **The node, unconditionally:** it has no unsupported parts. -/
theorem settled_all : ∀ p ∈ box.poses, Settled points symm p :=
  settled fun u hu ↦ by
    rw [List.length_eq_zero_iff.mp missing_length] at hu
    simp at hu

end Nieuwland.Results.Gen.ExternalTom7ChippedM18.Node6

/-!
## Node 7

The node at path `` of root 7: 1308 items in 1 chunk, 1308 of them checked (1308 checks);
unsupported: none.
-/

namespace Nieuwland.Results.Gen.ExternalTom7ChippedM18.Node7

/-- The box of the node. -/
def box : ChartBox :=
  ⟨1, 3, ⟨[-1, -1, -1, -1, -1], [1, 1, 1, 1, 1], 1⟩⟩

/-- The chunks: their boxes and unsupported parts. -/
def chunks : Cover (ChartBox × List (Unsupported ℤ)) :=
  (.leaf (Chunk7.box, Chunk7.missing))

theorem chunks_check : chunks.check (fun B c ↦ B.subset c.1) box = true := by
  decide +kernel

/-- The unsupported parts of all chunks. -/
def missing : List (Unsupported ℤ) :=
  chunks.data.flatMap Prod.snd

theorem missing_length : missing.length = 0 := by
  decide +kernel

/-- **The node.** Every pose of its box is settled, if the unsupported parts are. -/
theorem settled (hM : ∀ u ∈ missing, ∀ p ∈ u.region.poses,
    SettledRot points symm (Exact.rePre u.pre) p) :
    ∀ p ∈ box.poses, Settled points symm p :=
  Cover.settled_of_chunks (T := chunks)
    Chunk7.settled hM chunks_check

/-- **The node, unconditionally:** it has no unsupported parts. -/
theorem settled_all : ∀ p ∈ box.poses, Settled points symm p :=
  settled fun u hu ↦ by
    rw [List.length_eq_zero_iff.mp missing_length] at hu
    simp at hu

end Nieuwland.Results.Gen.ExternalTom7ChippedM18.Node7

/-!
## Node 8

The node at path `` of root 8: 65495 items in 2 chunks, 65495 of them checked (61458 checks);
unsupported: none.
-/

namespace Nieuwland.Results.Gen.ExternalTom7ChippedM18.Node8

/-- The box of the node. -/
def box : ChartBox :=
  ⟨2, 0, ⟨[-1, -1, -1, -1, -1], [1, 1, 1, 1, 1], 1⟩⟩

/-- The chunks: their boxes and unsupported parts. -/
def chunks : Cover (ChartBox × List (Unsupported ℤ)) :=
  (.split 0
    (.leaf (Chunk8.box, Chunk8.missing))
    (.leaf (Chunk9.box, Chunk9.missing)))

theorem chunks_check : chunks.check (fun B c ↦ B.subset c.1) box = true := by
  decide +kernel

/-- The unsupported parts of all chunks. -/
def missing : List (Unsupported ℤ) :=
  chunks.data.flatMap Prod.snd

theorem missing_length : missing.length = 0 := by
  decide +kernel

/-- **The node.** Every pose of its box is settled, if the unsupported parts are. -/
theorem settled (hM : ∀ u ∈ missing, ∀ p ∈ u.region.poses,
    SettledRot points symm (Exact.rePre u.pre) p) :
    ∀ p ∈ box.poses, Settled points symm p :=
  Cover.settled_of_chunks (T := chunks)
    ⟨Chunk8.settled, Chunk9.settled⟩ hM chunks_check

/-- **The node, unconditionally:** it has no unsupported parts. -/
theorem settled_all : ∀ p ∈ box.poses, Settled points symm p :=
  settled fun u hu ↦ by
    rw [List.length_eq_zero_iff.mp missing_length] at hu
    simp at hu

end Nieuwland.Results.Gen.ExternalTom7ChippedM18.Node8

/-!
## Node 9

The node at path `` of root 9: 10289 items in 1 chunk, 10289 of them checked (10289 checks);
unsupported: none.
-/

namespace Nieuwland.Results.Gen.ExternalTom7ChippedM18.Node9

/-- The box of the node. -/
def box : ChartBox :=
  ⟨2, 1, ⟨[-1, -1, -1, -1, -1], [1, 1, 1, 1, 1], 1⟩⟩

/-- The chunks: their boxes and unsupported parts. -/
def chunks : Cover (ChartBox × List (Unsupported ℤ)) :=
  (.leaf (Chunk10.box, Chunk10.missing))

theorem chunks_check : chunks.check (fun B c ↦ B.subset c.1) box = true := by
  decide +kernel

/-- The unsupported parts of all chunks. -/
def missing : List (Unsupported ℤ) :=
  chunks.data.flatMap Prod.snd

theorem missing_length : missing.length = 0 := by
  decide +kernel

/-- **The node.** Every pose of its box is settled, if the unsupported parts are. -/
theorem settled (hM : ∀ u ∈ missing, ∀ p ∈ u.region.poses,
    SettledRot points symm (Exact.rePre u.pre) p) :
    ∀ p ∈ box.poses, Settled points symm p :=
  Cover.settled_of_chunks (T := chunks)
    Chunk10.settled hM chunks_check

/-- **The node, unconditionally:** it has no unsupported parts. -/
theorem settled_all : ∀ p ∈ box.poses, Settled points symm p :=
  settled fun u hu ↦ by
    rw [List.length_eq_zero_iff.mp missing_length] at hu
    simp at hu

end Nieuwland.Results.Gen.ExternalTom7ChippedM18.Node9

/-!
## Node 10

The node at path `` of root 10: 12696 items in 1 chunk, 12696 of them checked (12697 checks);
unsupported: none.
-/

namespace Nieuwland.Results.Gen.ExternalTom7ChippedM18.Node10

/-- The box of the node. -/
def box : ChartBox :=
  ⟨2, 2, ⟨[-1, -1, -1, -1, -1], [1, 1, 1, 1, 1], 1⟩⟩

/-- The chunks: their boxes and unsupported parts. -/
def chunks : Cover (ChartBox × List (Unsupported ℤ)) :=
  (.leaf (Chunk11.box, Chunk11.missing))

theorem chunks_check : chunks.check (fun B c ↦ B.subset c.1) box = true := by
  decide +kernel

/-- The unsupported parts of all chunks. -/
def missing : List (Unsupported ℤ) :=
  chunks.data.flatMap Prod.snd

theorem missing_length : missing.length = 0 := by
  decide +kernel

/-- **The node.** Every pose of its box is settled, if the unsupported parts are. -/
theorem settled (hM : ∀ u ∈ missing, ∀ p ∈ u.region.poses,
    SettledRot points symm (Exact.rePre u.pre) p) :
    ∀ p ∈ box.poses, Settled points symm p :=
  Cover.settled_of_chunks (T := chunks)
    Chunk11.settled hM chunks_check

/-- **The node, unconditionally:** it has no unsupported parts. -/
theorem settled_all : ∀ p ∈ box.poses, Settled points symm p :=
  settled fun u hu ↦ by
    rw [List.length_eq_zero_iff.mp missing_length] at hu
    simp at hu

end Nieuwland.Results.Gen.ExternalTom7ChippedM18.Node10

/-!
## Node 11

The node at path `` of root 11: 13787 items in 1 chunk, 13787 of them checked (13787 checks);
unsupported: none.
-/

namespace Nieuwland.Results.Gen.ExternalTom7ChippedM18.Node11

/-- The box of the node. -/
def box : ChartBox :=
  ⟨2, 3, ⟨[-1, -1, -1, -1, -1], [1, 1, 1, 1, 1], 1⟩⟩

/-- The chunks: their boxes and unsupported parts. -/
def chunks : Cover (ChartBox × List (Unsupported ℤ)) :=
  (.leaf (Chunk12.box, Chunk12.missing))

theorem chunks_check : chunks.check (fun B c ↦ B.subset c.1) box = true := by
  decide +kernel

/-- The unsupported parts of all chunks. -/
def missing : List (Unsupported ℤ) :=
  chunks.data.flatMap Prod.snd

theorem missing_length : missing.length = 0 := by
  decide +kernel

/-- **The node.** Every pose of its box is settled, if the unsupported parts are. -/
theorem settled (hM : ∀ u ∈ missing, ∀ p ∈ u.region.poses,
    SettledRot points symm (Exact.rePre u.pre) p) :
    ∀ p ∈ box.poses, Settled points symm p :=
  Cover.settled_of_chunks (T := chunks)
    Chunk12.settled hM chunks_check

/-- **The node, unconditionally:** it has no unsupported parts. -/
theorem settled_all : ∀ p ∈ box.poses, Settled points symm p :=
  settled fun u hu ↦ by
    rw [List.length_eq_zero_iff.mp missing_length] at hu
    simp at hu

end Nieuwland.Results.Gen.ExternalTom7ChippedM18.Node11

/-!
## The certificate

The roots cover the twelve unit chart boxes (`unitsIn`), and every pose of every root is settled:
the polyhedron is not Rupert (`Polyhedron.not_isRupert_of_roots`), and scaled back
(`Nieuwland.Results.Gen.ExternalTom7ChippedM18.eq_smul`), so is `Other.Tom7ChippedM18.polyhedron`.
-/

namespace Nieuwland.Results.Gen.ExternalTom7ChippedM18

/-- The roots of the cover. -/
def roots : List ChartBox :=
  [Node0.box, Node1.box, Node2.box, Node3.box, Node4.box, Node5.box, Node6.box, Node7.box,
   Node8.box, Node9.box, Node10.box, Node11.box]

/-- **The certificate**: the polyhedron of Lean's points is not Rupert. -/
theorem not_isRupert : ¬ (Polyhedron.ofPoints points).IsRupert :=
  Polyhedron.not_isRupert_of_roots span_ok (roots := roots) (by decide +kernel)
    ⟨Node0.settled_all, Node1.settled_all, Node2.settled_all, Node3.settled_all, Node4.settled_all,
    Node5.settled_all, Node6.settled_all, Node7.settled_all, Node8.settled_all, Node9.settled_all,
    Node10.settled_all, Node11.settled_all⟩

end Nieuwland.Results.Gen.ExternalTom7ChippedM18

namespace Nieuwland.Polyhedra

/-- **Chipped M18 (Tom 7) is not Rupert.** -/
theorem externalTom7ChippedM18_not_isRupert : ¬ Other.Tom7ChippedM18.polyhedron.IsRupert := by
  rw [Nieuwland.Results.Gen.ExternalTom7ChippedM18.eq_smul, Polyhedron.isRupert_smul_iff (by norm_num)]
  exact Nieuwland.Results.Gen.ExternalTom7ChippedM18.not_isRupert

/-- **The Nieuwland number of Chipped M18 (Tom 7) is 1**: it is full-dimensional (`Nieuwland.Results.Gen.ExternalTom7ChippedM18.span_ok`) and not
Rupert, so no copy of a ratio above 1 passes through it and every smaller one does. -/
theorem externalTom7ChippedM18_nieuwland : Other.Tom7ChippedM18.polyhedron.nieuwland = 1 := by
  refine Polyhedron.nieuwland_eq_one_of_not_isRupert ?_ externalTom7ChippedM18_not_isRupert
  rw [Nieuwland.Results.Gen.ExternalTom7ChippedM18.eq_smul]
  exact (Check.Polyhedron.fullDim_of_spanOk Nieuwland.Results.Gen.ExternalTom7ChippedM18.span_ok).smul (by norm_num)

/-- Chipped M18 (Tom 7): the exact Nieuwland number in the list form of `Modules/System/System.lean`: the
largest scale `x 0` of the solutions of the system `x 0 = 1` (no box), its one scale, and so
between these decimals. -/
theorem externalTom7ChippedM18_exact_list :
    PolynomialSystem.IsMaxSingle [⟨[([(1, [(0, 1)])], [(1, [])])], []⟩] Other.Tom7ChippedM18.polyhedron.nieuwland ∧
      Other.Tom7ChippedM18.polyhedron.nieuwland ∈ Set.Icc ((1000000000000000000000000000000 : ℝ) / 10 ^ 30)
        ((1000000000000000000000000000000 : ℝ) / 10 ^ 30) := by
  obtain ⟨h, h1, h2⟩ := isMaxSingle_scales_one externalTom7ChippedM18_nieuwland
  exact ⟨h, le_trans (by norm_num) h1, le_trans h2 (by norm_num)⟩

section

open scoped Nieuwland.Notation

/-- **Chipped M18 (Tom 7): the exact Nieuwland number `ν Other.Tom7ChippedM18.polyhedron`**: the largest scale `ℓ` of the real solutions
of `ℓ - 1 = 0`, and its decimals (the statement of `Modules/System/Readable.lean`, from
`externalTom7ChippedM18_exact_list`). -/
theorem externalTom7ChippedM18_exact :
    IsGreatest {ℓ : ℝ | ℓ - 1 = 0}
      (ν Other.Tom7ChippedM18.polyhedron) ∧
      ν Other.Tom7ChippedM18.polyhedron ∈ Set.Icc ((1000000000000000000000000000000 : ℝ) / 10 ^ 30)
        ((1000000000000000000000000000000 : ℝ) / 10 ^ 30) :=
  ⟨Readable.isGreatest [0] (by decide +kernel) externalTom7ChippedM18_exact_list.1.1, externalTom7ChippedM18_exact_list.2⟩

/-- **The Nieuwland number of `Other.Tom7ChippedM18.polyhedron`**: `ν Other.Tom7ChippedM18.polyhedron` lies in `[k, k + 1] / 10 ^ 30`, and it is the
largest value of the first variable over the real solutions of finitely many systems of integer
polynomial equations in rational intervals, each system's solutions with one value of it
(`IsPolynomialSystemMax`, `Modules/System/PolyMax.lean`); `externalTom7ChippedM18_exact` writes the system out. -/
theorem externalTom7ChippedM18_nu :
    ν Other.Tom7ChippedM18.polyhedron ∈ Set.Icc ((1000000000000000000000000000000 : ℝ) / 10 ^ 30) ((1000000000000000000000000000001 : ℝ) / 10 ^ 30) ∧
      IsPolynomialSystemMax (ν Other.Tom7ChippedM18.polyhedron) :=
  ⟨PolynomialSystem.mem_Icc_dec 1000000000000000000000000000000 1000000000000000000000000000000 1000000000000000000000000000000 1000000000000000000000000000001 30 ⟨externalTom7ChippedM18_exact_list.1.1, externalTom7ChippedM18_exact_list.2⟩ (by decide +kernel),
   PolynomialSystem.isPolynomialSystemMax (by decide +kernel) externalTom7ChippedM18_exact_list.1⟩

end

end Nieuwland.Polyhedra
