module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Quasicoherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal.AssociatedGraded
public import ReasLib.AlgebraicGeometry.RingedSpace.Definition
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Conormal algebras of scheme morphisms

The conormal algebra is the associated graded algebra sheaf of the kernel of the
inverse-image structure-sheaf map.  Its homogeneous pieces are canonically the
sheafified scalar extensions of the successive kernel-ideal quotients.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

open SheafOfModules.RingedSite

variable {X Z : Scheme.{u}}

/-- The conormal algebra of a scheme morphism, formed as the associated graded algebra
sheaf of the kernel of its inverse-image structure-sheaf map. -/
noncomputable def ConormalAlgebra (f : Z ⟶ X) :
    GradedAlgebraSheaf.{u, u} Z.sheaf ℕ :=
  KernelIdeal.AssociatedGraded.algebra.{u, u}
    (RingedSpace.Hom.inverseImageStructureSheafHomComm f.toShHom)

namespace ConormalAlgebra

/-- The degree-`n` piece of a conormal algebra is canonically the sheafification of the
scalar-extended quotient of the `n`-th kernel-ideal power by the next power. -/
noncomputable def pieceIso (f : Z ⟶ X) (n : ℕ) :
    (ConormalAlgebra f).obj n ≅
      KernelIdeal.AssociatedGraded.pieceSheaf.{u, u}
        (RingedSpace.Hom.inverseImageStructureSheafHomComm f.toShHom) n :=
  KernelIdeal.AssociatedGraded.gradePieceSheafIso.{u, u}
    (RingedSpace.Hom.inverseImageStructureSheafHomComm f.toShHom) n

/-- Every homogeneous piece of the conormal algebra of an immersion is quasi-coherent. -/
theorem isQuasicoherent (f : Z ⟶ X) [IsImmersion f] :
    (ConormalAlgebra f).IsQuasicoherent := sorry

/-- Each degree of the conormal algebra of an immersion is a quasi-coherent module sheaf. -/
instance instIsQuasicoherentObj (f : Z ⟶ X) [IsImmersion f] (n : ℕ) :
    ((ConormalAlgebra f).obj n).IsQuasicoherent :=
  isQuasicoherent f n

end ConormalAlgebra

end AlgebraicGeometry.Scheme
