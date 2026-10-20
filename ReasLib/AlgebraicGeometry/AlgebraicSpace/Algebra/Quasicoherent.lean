module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRing

/-!
# Quasi-coherent algebras on an algebraic space

An algebra under the canonical commutative structure sheaf is quasi-coherent
when its underlying module is quasi-coherent on the small étale site.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Quasi-coherence of the module underlying an algebra over the canonical structure sheaf. -/
abbrev qcAlgebraUnderProperty {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ObjectProperty (Under (commStructureSheaf X)) :=
  fun A ↦
    ((restrictionAlong A.hom).obj
      (unitModule (smallEtaleTopology X)
        (A.right : Sheaf (smallEtaleTopology X) CommRingCat.{u}))).IsQuasicoherent

/-- The full subcategory of quasi-coherent algebras over the canonical structure sheaf. -/
abbrev QcAlgebraUnder {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  (qcAlgebraUnderProperty X).FullSubcategory

namespace QcAlgebraUnder

/-- Forget quasi-coherence and retain the given algebra map. -/
abbrev forget {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.QcAlgebraUnder ⥤ Under (commStructureSheaf X) :=
  (qcAlgebraUnderProperty X).ι

/-- The actual commutative-ring sheaf underlying a quasi-coherent algebra. -/
abbrev sheaf {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} :=
  A.obj.right

/-- Sections of the algebra on an étale chart. -/
abbrev sectionRing {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder)
    (U : smallEtaleSite X) : CommRingCat.{u} :=
  A.obj.right.obj.obj (op U)

/-- The given structure homomorphism on an étale chart. -/
abbrev structureMap {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder)
    (U : smallEtaleSite X) :
    (commStructureSheaf X).obj.obj (op U) ⟶ sectionRing A U :=
  (InducedCategory.Hom.hom A.obj.hom).app (op U)

/-- The algebra structure on sections is induced by the given structure homomorphism. -/
instance instAlgebra {S : Scheme.{u}} {X : AlgebraicSpace S} (A : X.QcAlgebraUnder)
    (U : smallEtaleSite X) : Algebra Γ(U.left.left, ⊤) (sectionRing A U) :=
  (structureMap A U).hom.toAlgebra

/-- The structure sheaf as a quasi-coherent algebra over itself. -/
def structureQcAlgebra {S : Scheme.{u}} (X : AlgebraicSpace S) : X.QcAlgebraUnder where
  obj := Under.mk (𝟙 (commStructureSheaf X))
  property := sorry

/-- The underlying restricted unit module is quasi-coherent by the algebra's stored property. -/
theorem isQuasicoherent_restrictedUnit {S : Scheme.{u}} {X : AlgebraicSpace S}
    (A : X.QcAlgebraUnder) :
    ((restrictionAlong A.obj.hom).obj
      (unitModule (smallEtaleTopology X) (sheaf A))).IsQuasicoherent :=
  A.property

end QcAlgebraUnder

end AlgebraicGeometry.AlgebraicSpace
