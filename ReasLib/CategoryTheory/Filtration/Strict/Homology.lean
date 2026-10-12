/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import ReasLib.CategoryTheory.Filtration.Strict.Subquotient
public import ReasLib.CategoryTheory.Filtration.Strict.Abelian
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Homology of Strict Complexes of Filtered Objects

For a two-step complex of filtered objects with strict differentials, this file presents the
graded piece of `ker β / im α` as a left homology datum for the associated graded complex.
The resulting comparison with `ShortComplex.homology` is therefore supplied by Mathlib's
canonical homology-data API rather than by an ad hoc isomorphism construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory.FilteredObject.Hom

open FilteredObject

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A B D : FilteredObject C}

namespace Graded

namespace ShortComplex

/-- The short complex on the `p`-th graded pieces induced by a two-step filtered complex. -/
noncomputable abbrev of
    (f : A ⟶ B) (g : B ⟶ D) (hfg : f ≫ g = 0) (p : ℤ) : ShortComplex C :=
  ShortComplex.mk (gradedPieceMap f p) (gradedPieceMap g p)
    (gradedPieceMap_comp_zero f g hfg p)

end ShortComplex

namespace Kernel

namespace Cycles

/-- The canonical graded kernel fork associated to a filtered morphism. -/
noncomputable def fork (g : B ⟶ D) (p : ℤ) :
    KernelFork (gradedPieceMap g p) :=
  KernelFork.ofι (gradedPieceMap (kernelι g) p)
    (gradedPieceMap_comp_zero (kernelι g) g (kernelι_comp g) p)

end Cycles

/-- Strictness makes the canonical graded kernel row exact. -/
theorem exact_of_strict (g : B ⟶ D) (hg : Strict g) (p : ℤ) :
    (Graded.Kernel.shortComplex g p).Exact := sorry

namespace Cycles

/-- Strictness identifies the graded piece of the filtered kernel with the kernel of the
induced map on graded pieces. -/
noncomputable def isLimit_of_strict (g : B ⟶ D) (hg : Strict g) (p : ℤ) :
    IsLimit (fork g p) :=
  Graded.Kernel.isKernel g p (exact_of_strict g hg p)

end Cycles

end Kernel

namespace ShortComplex

namespace Cycles

/-- The boundary map from `gr^p A` to the canonical graded cycles object. -/
noncomputable def boundaryTo
    (f : A ⟶ B) (g : B ⟶ D) (hfg : f ≫ g = 0) (hg : Strict g) (p : ℤ) :
    A.gradedPiece p ⟶ (kernel g).gradedPiece p :=
  (Kernel.Cycles.isLimit_of_strict g hg p).lift
    (KernelFork.ofι (gradedPieceMap f p) (gradedPieceMap_comp_zero f g hfg p))

/-- The boundary-to-cycles map followed by the graded kernel inclusion is the original graded
boundary map. -/
theorem boundaryTo_comp_kernel
    (f : A ⟶ B) (g : B ⟶ D) (hfg : f ≫ g = 0) (hg : Strict g) (p : ℤ) :
    boundaryTo f g hfg hg p ≫ gradedPieceMap (kernelι g) p =
      gradedPieceMap f p := sorry

end Cycles

namespace Homology

/-- The canonical projection from graded cycles to the graded piece of `ker g / im f`. -/
noncomputable def projection
    (f : A ⟶ B) (g : B ⟶ D) (hfg : f ≫ g = 0) (p : ℤ) :
    (kernel g).gradedPiece p ⟶
      (FilteredObject.Subobject.Subquotient.object B
        (image_le_kernel f.hom g.hom (hom_comp_eq_zero f g hfg))).gradedPiece p :=
  gradedPieceMap
    (FilteredObject.Subobject.Subquotient.map B
      (image_le_kernel f.hom g.hom (hom_comp_eq_zero f g hfg))) p

/-- Graded boundaries vanish under the canonical projection to the graded subquotient. -/
theorem boundaryTo_comp_projection
    (f : A ⟶ B) (g : B ⟶ D) (hfg : f ≫ g = 0)
    (hg : Strict g) (p : ℤ) :
    Cycles.boundaryTo f g hfg hg p ≫ projection f g hfg p = 0 := sorry

/-- For strict differentials, graded boundaries, graded cycles, and the graded subquotient form
a short exact sequence. -/
theorem shortExact
    (f : A ⟶ B) (g : B ⟶ D) (hfg : f ≫ g = 0)
    (hf : Strict f) (hg : Strict g) (p : ℤ) :
    (ShortComplex.mk (Cycles.boundaryTo f g hfg hg p)
      (projection f g hfg p)
      (boundaryTo_comp_projection f g hfg hg p)).ShortExact := sorry

/-- The canonical projection from graded cycles to `gr^p (ker g / im f)` is the cokernel of
the graded boundary-to-cycles map. -/
noncomputable def projectionIsCokernel
    (f : A ⟶ B) (g : B ⟶ D) (hfg : f ≫ g = 0)
    (hf : Strict f) (hg : Strict g) (p : ℤ) :
    IsColimit
      (CokernelCofork.ofπ (projection f g hfg p)
        (boundaryTo_comp_projection f g hfg hg p)) :=
  (shortExact f g hfg hf hg p).gIsCokernel

/-- The graded subquotient `gr^p (ker g / im f)` as concrete left homology data for the graded
short complex. -/
@[stacks 0128]
noncomputable def data
  (f : A ⟶ B) (g : B ⟶ D) (hfg : f ≫ g = 0)
    (hf : Strict f) (hg : Strict g) (p : ℤ) :
    (Graded.ShortComplex.of f g hfg p).LeftHomologyData where
  K := (kernel g).gradedPiece p
  H := (FilteredObject.Subobject.Subquotient.object B
    (image_le_kernel f.hom g.hom (hom_comp_eq_zero f g hfg))).gradedPiece p
  i := gradedPieceMap (kernelι g) p
  π := projection f g hfg p
  wi := gradedPieceMap_comp_zero (kernelι g) g (kernelι_comp g) p
  hi := Kernel.Cycles.isLimit_of_strict g hg p
  wπ := boundaryTo_comp_projection f g hfg hg p
  hπ := projectionIsCokernel f g hfg hf hg p

/-- The canonical identification of `gr^p (ker g / im f)` with the homology of the graded short
complex. -/
@[stacks 0128]
noncomputable def iso
    (f : A ⟶ B) (g : B ⟶ D) (hfg : f ≫ g = 0)
    (hf : Strict f) (hg : Strict g) (p : ℤ) :
    (FilteredObject.Subobject.Subquotient.object B
      (image_le_kernel f.hom g.hom (hom_comp_eq_zero f g hfg))).gradedPiece p ≅
      (Graded.ShortComplex.of f g hfg p).homology :=
  (data f g hfg hf hg p).homologyIso.symm

end Homology

end ShortComplex

end Graded

end CategoryTheory.FilteredObject.Hom
