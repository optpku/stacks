/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tensor

/-!
# Restricted scalar extension on homological complexes

@stack 09PQ

The natural identification of restriction after extension of scalars with tensoring by the
target algebra lifts degreewise to homological complexes.  This leaf records the functor-level
comparison, its objectwise form, and the induced comparison on homology.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory

universe u w

namespace ModuleCat.ExtendScalars

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type w} {c : ComplexShape ι}

/-- Restriction after extension of scalars, applied degreewise to a homological complex. -/
@[stacks 09PQ "restricted scalar extension complex"]
abbrev restrictedComplex (K : HomologicalComplex (ModuleCat R) c) :
    HomologicalComplex (ModuleCat R) c :=
  ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex c).obj
    (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex c).obj K)

/-- Tensoring a homological complex degreewise by the underlying `R`-module of `S`. -/
@[stacks 09PQ "tensor complex over the target algebra"]
abbrev tensorComplex (K : HomologicalComplex (ModuleCat R) c) :
    HomologicalComplex (ModuleCat R) c :=
  ((tensorLeft (ModuleCat.of R S)).mapHomologicalComplex c).obj K

/-- Tag 09PQ: restriction after extension of scalars on homological complexes is naturally
isomorphic to degreewise tensoring by the target algebra. -/
@[stacks 09PQ "restricted scalar extension on homological complexes"]
noncomputable def restrictTensorComplexNatIso (c : ComplexShape ι) :
    (ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex c ⋙
        (ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex c ≅
      (tensorLeft (ModuleCat.of R S)).mapHomologicalComplex c :=
  Functor.mapHomologicalComplexCompIso
    (restrictTensorNatIso (R := R) (S := S)) c

/-- The objectwise complex comparison induced by `restrictTensorComplexNatIso`. -/
@[stacks 09PQ "restricted scalar extension of a homological complex"]
noncomputable def restrictTensorComplexIso
    (K : HomologicalComplex (ModuleCat R) c) :
    restrictedComplex (S := S) K ≅ tensorComplex (S := S) K :=
  (restrictTensorComplexNatIso (R := R) (S := S) c).app K

/-- The component in degree `i` of the complex comparison is the module-level restricted
scalar-extension comparison. -/
@[simp, stacks 09PQ "degreewise restricted scalar extension comparison"]
theorem restrictTensorComplexIso_app
    (K : HomologicalComplex (ModuleCat R) c) (i : ι) :
    HomologicalComplex.Hom.isoApp
        (restrictTensorComplexIso (S := S) K) i =
      restrictTensorIso (R := R) (S := S) (K.X i) := sorry

/-- The restricted scalar-extension complex comparison is natural in the complex. -/
@[reassoc]
theorem restrictTensorComplexIso_hom_naturality
    {K L : HomologicalComplex (ModuleCat R) c} (f : K ⟶ L) :
    ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex c).map
          (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex c).map f) ≫
        (restrictTensorComplexIso (S := S) L).hom =
      (restrictTensorComplexIso (S := S) K).hom ≫
        ((tensorLeft (ModuleCat.of R S)).mapHomologicalComplex c).map f := sorry

/-- Tag 09PQ: homology after restricting an extended complex is canonically the homology of
the degreewise tensor complex. -/
@[stacks 09PQ "homology of restricted scalar extension"]
noncomputable def restrictTensorHomologyIso
    (K : HomologicalComplex (ModuleCat R) c) (i : ι) :
    (restrictedComplex (S := S) K).homology i ≅
      (tensorComplex (S := S) K).homology i :=
  HomologicalComplex.homologyMapIso (restrictTensorComplexIso (S := S) K) i

/-- The restricted scalar-extension homology comparison is natural in maps of complexes. -/
@[reassoc]
theorem restrictTensorHomologyIso_hom_naturality
    {K L : HomologicalComplex (ModuleCat R) c} (f : K ⟶ L) (i : ι) :
    HomologicalComplex.homologyMap
          (((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex c).map
            (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex c).map f)) i ≫
        (restrictTensorHomologyIso (S := S) L i).hom =
      (restrictTensorHomologyIso (S := S) K i).hom ≫
        HomologicalComplex.homologyMap
          (((tensorLeft (ModuleCat.of R S)).mapHomologicalComplex c).map f) i := sorry

end ModuleCat.ExtendScalars
