module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import stacks_project.Chap66.Definition_66_29_1_RingedSite

/-!
# Quasi-coherent algebras on an algebraic space

This file packages quasi-coherent sheaves of `𝒪_X`-algebras on the small étale site of an
algebraic space `X` as the full subcategory of algebras under the commutative structure sheaf
whose restricted unit module is quasi-coherent.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Commutative-ring-valued sheaf composition exists on the small étale topology of an algebraic
space. -/
instance smallEtaleTopology_hasSheafCompose_commRingCat {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    (smallEtaleTopology X).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) :=
  sorry

/-- The commutative structure presheaf on the small étale site of `X`, sending an étale object
`U` to `Γ(U, ⊤)`. -/
def commRingStructurePresheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (smallEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u} where
  obj U := Γ(U.unop.left.left, ⊤)
  map {U V} f := f.unop.left.left.appTop
  map_id _ := sorry
  map_comp _ _ := sorry

/-- The value of `commRingStructurePresheaf X` at `U` is `Γ(U, ⊤)`. -/
theorem commRingStructurePresheaf_obj {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallEtaleSite X) :
    (commRingStructurePresheaf X).obj (op U) = Γ(U.left.left, ⊤) :=
  sorry

/-- The commutative structure presheaf on the small étale site of an algebraic space is a
sheaf. -/
theorem commRingStructurePresheaf_isSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Presheaf.IsSheaf (smallEtaleTopology X) (commRingStructurePresheaf X) :=
  sorry

/-- The commutative structure sheaf `𝒪_X` on the small étale site of an algebraic space. -/
def commRingStructureSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} where
  obj := commRingStructurePresheaf X
  property := commRingStructurePresheaf_isSheaf X

/-- On a scheme étale over `X`, the commutative structure sheaf has value `Γ(U, ⊤)`. -/
theorem commRingStructureSheaf_obj {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallEtaleSite X) :
    (commRingStructureSheaf X).obj.obj (op U) = Γ(U.left.left, ⊤) :=
  sorry

/-- Forgetting commutativity in `commRingStructureSheaf X` recovers the ring-valued structure
sheaf `𝒪_X`. -/
theorem forget₂_commRingStructureSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (sheafCompose (smallEtaleTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (commRingStructureSheaf X) =
      structureSheaf X :=
  sorry

/-- The property of an `𝒪_X`-algebra whose underlying `𝒪_X`-module is quasi-coherent. -/
abbrev qcAlgebraUnderProperty {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ObjectProperty (Under (commRingStructureSheaf X)) :=
  fun A ↦
    ((restrictionAlong A.hom).obj
      (unitModule (smallEtaleTopology X)
        (A.right : Sheaf (smallEtaleTopology X) CommRingCat.{u}))).IsQuasicoherent

/-- The category of quasi-coherent `𝒪_X`-algebras on an algebraic space. -/
abbrev QcAlgebraUnder {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  (qcAlgebraUnderProperty X).FullSubcategory

namespace QcAlgebraUnder

/-- The forgetful functor from quasi-coherent `𝒪_X`-algebras to all `𝒪_X`-algebras. -/
abbrev forget {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.QcAlgebraUnder ⥤ Under (commRingStructureSheaf X) :=
  (qcAlgebraUnderProperty X).ι

/-- The commutative-ring sheaf underlying a quasi-coherent `𝒪_X`-algebra. -/
abbrev sheaf {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} :=
  A.obj.right

/-- The ring of sections of a quasi-coherent `𝒪_X`-algebra on an étale object of `X`. -/
abbrev sectionRing {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder)
    (U : smallEtaleSite X) : CommRingCat.{u} :=
  A.obj.right.obj.obj (op U)

/-- The structure map from sections of `𝒪_X` to sections of a quasi-coherent algebra. -/
abbrev structureMap {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder)
    (U : smallEtaleSite X) :
    (commRingStructureSheaf X).obj.obj (op U) ⟶ sectionRing A U :=
  (InducedCategory.Hom.hom A.obj.hom).app (op U)

/-- The algebra structure on sections of `A` over `U` induced by the structure map. -/
instance instAlgebra {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder)
    (U : smallEtaleSite X) :
    Algebra Γ(U.left.left, ⊤) (sectionRing A U) :=
  (structureMap A U).hom.toAlgebra

/-- The structure sheaf `𝒪_X`, as a quasi-coherent algebra over itself. -/
def structureQcAlgebra {S : Scheme.{u}} (X : AlgebraicSpace S) : X.QcAlgebraUnder where
  obj := Under.mk (𝟙 (commRingStructureSheaf X))
  property := sorry

/-- The module underlying a quasi-coherent `𝒪_X`-algebra is quasi-coherent. -/
theorem isQuasicoherent_restrictedUnit {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) :
    ((restrictionAlong A.obj.hom).obj
      (unitModule (smallEtaleTopology X) (sheaf A))).IsQuasicoherent :=
  sorry

end QcAlgebraUnder

end AlgebraicGeometry.AlgebraicSpace
