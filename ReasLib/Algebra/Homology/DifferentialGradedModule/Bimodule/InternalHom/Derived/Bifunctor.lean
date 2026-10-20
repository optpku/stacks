module

public import Mathlib.CategoryTheory.Localization.Opposite
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom.Derived.Naturality
public import ReasLib.CategoryTheory.Localization.Lifting.CommShift

/-!
# Derived Internal Hom as a Bifunctor

Total derived internal Hom is contravariant in a bimodule. This file performs that
localization once at the reusable derived-bimodule layer; consumers may then compose the
result with homology or other functors without choosing another localization lift.
-/

@[expose] public section

noncomputable section

universe u v w x

open CategoryTheory Opposite

namespace DifferentialGradedBimodule.InternalHom

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R} {B : CochainDGAlgebra.{u, x} R}

/-- Total derived internal Hom, contravariantly functorial in the full derived category of
(A, B)-bimodules. -/
@[stacks 0BYV "derived internal Hom on the derived bimodule category"]
noncomputable def derivedBifunctor
    (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) :
    (DifferentialGradedBimodule.Derived.Category.{u, v, w, x} A B)ᵒᵖ ⥤
      (DifferentialGradedModule.Derived.Category.{u, v} B ⥤
        DifferentialGradedModule.Derived.Category.{u, v} A) :=
  Localization.lift (derivedBimoduleFunctor A B)
    (derivedBimoduleFunctor_inverts A B)
    (DifferentialGradedBimodule.Derived.fromBimodules A B).op

/-- Pulling derivedBifunctor back to strict bimodules recovers the strict parameter functor. -/
@[stacks 0BYV "strict factorization of derived internal Hom"]
noncomputable def derivedBifunctorFactors
    (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) :
    (DifferentialGradedBimodule.Derived.fromBimodules A B).op ⋙
        derivedBifunctor A B ≅
      derivedBimoduleFunctor A B :=
  Localization.fac (derivedBimoduleFunctor A B)
    (derivedBimoduleFunctor_inverts A B)
    (DifferentialGradedBimodule.Derived.fromBimodules A B).op

/-- derivedBifunctor is the chosen localization lift of the strict derived internal-Hom
parameter functor. -/
@[stacks 0BYV "localization lift of the derived internal-Hom parameter"]
noncomputable instance derivedBifunctorLifting
    (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) :
    Localization.Lifting
      (DifferentialGradedBimodule.Derived.fromBimodules A B).op
      (DifferentialGradedBimodule.quasiIso A B).op
      (derivedBimoduleFunctor A B) (derivedBifunctor A B) :=
  ⟨derivedBifunctorFactors A B⟩

/-- Derived internal Hom is additive in its opposite derived-bimodule variable. -/
@[stacks 0BYV "additivity of derived internal Hom in the derived bimodule"]
noncomputable instance derivedBifunctorAdditive
    (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) :
    (derivedBifunctor A B).Additive := sorry

/-- Derived internal Hom is R-linear in its opposite derived-bimodule variable. -/
@[stacks 0BYV "linearity of derived internal Hom in the derived bimodule"]
noncomputable instance derivedBifunctorLinear
    (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) :
    Functor.Linear R (derivedBifunctor A B) := sorry

/-- Fixing a derived bimodule in derivedBifunctor gives an additive functor of the target. -/
@[stacks 0BYV "additivity of derived internal Hom at a derived bimodule"]
noncomputable instance derivedBifunctorObjAdditive
    (T : (DifferentialGradedBimodule.Derived.Category.{u, v, w, x} A B)ᵒᵖ) :
    ((derivedBifunctor A B).obj T).Additive := sorry

/-- Fixing a derived bimodule in derivedBifunctor gives an R-linear functor of the target. -/
@[stacks 0BYV "linearity of derived internal Hom at a derived bimodule"]
noncomputable instance derivedBifunctorObjLinear
    (T : (DifferentialGradedBimodule.Derived.Category.{u, v, w, x} A B)ᵒᵖ) :
    Functor.Linear R ((derivedBifunctor A B).obj T) := sorry

/-- Fixing an opposite derived bimodule gives an internal-Hom functor that commutes with
integer shifts. -/
@[stacks 0BYV "shift compatibility of derived internal Hom at a derived bimodule"]
noncomputable instance derivedBifunctorObjCommShift
    (T : (DifferentialGradedBimodule.Derived.Category.{u, v, w, x} A B)ᵒᵖ) :
    ((derivedBifunctor A B).obj T).CommShift ℤ :=
  Localization.Lifting.objCommShift
    (L := (DifferentialGradedBimodule.Derived.fromBimodules A B).op)
    (W := (DifferentialGradedBimodule.quasiIso A B).op)
    (F := derivedBimoduleFunctor A B) (F' := derivedBifunctor A B)
    (fun X ↦ derivedFunctor_commShift X.unop) T

/-- Fixing an opposite derived bimodule gives a triangulated derived internal-Hom functor. -/
@[stacks 0BYV "triangulated derived internal Hom at a derived bimodule"]
instance derivedBifunctorObjIsTriangulated
    (T : (DifferentialGradedBimodule.Derived.Category.{u, v, w, x} A B)ᵒᵖ) :
    ((derivedBifunctor A B).obj T).IsTriangulated := sorry

/-- At the derived image of a strict bimodule, derivedBifunctor recovers its fixed-source
total derived internal-Hom functor. -/
@[stacks 0BYV "derived internal Hom at a strict bimodule"]
noncomputable def derivedBifunctorObjIso
    (T : DifferentialGradedBimodule.{u, v, w, x} A B) :
    (derivedBifunctor A B).obj
        (op (DifferentialGradedBimodule.Derived.object T)) ≅
      derivedFunctor T :=
  (derivedBifunctorFactors A B).app (op T)

/-- The forward strict-representative comparison is natural under contravariant
precomposition. -/
@[reassoc (attr := simp), stacks 0BYV "naturality of the strict derived internal-Hom comparison"]
theorem derivedBifunctorObjIso.hom_naturality
    {T T' : DifferentialGradedBimodule.{u, v, w, x} A B} (f : T ⟶ T') :
    (derivedBifunctor A B).map
          ((DifferentialGradedBimodule.Derived.fromBimodules A B).map f).op ≫
        (derivedBifunctorObjIso T).hom =
      (derivedBifunctorObjIso T').hom ≫ derivedNatTrans f := sorry

/-- The inverse strict-representative comparison is natural under contravariant
precomposition. -/
@[reassoc (attr := simp), stacks 0BYV "inverse naturality of the strict derived internal-Hom comparison"]
theorem derivedBifunctorObjIso.inv_naturality
    {T T' : DifferentialGradedBimodule.{u, v, w, x} A B} (f : T ⟶ T') :
    derivedNatTrans f ≫ (derivedBifunctorObjIso T).inv =
      (derivedBifunctorObjIso T').inv ≫
        (derivedBifunctor A B).map
          ((DifferentialGradedBimodule.Derived.fromBimodules A B).map f).op := sorry

/-- On a strict bimodule morphism, the descended action is conjugate to the canonical derived
precomposition transformation by the factorization isomorphisms. -/
@[stacks 0BYV "derived internal Hom on a strict bimodule morphism"]
theorem derivedBifunctor_map_fromBimodules
    {T T' : DifferentialGradedBimodule.{u, v, w, x} A B} (f : T ⟶ T') :
    (derivedBifunctor A B).map
        ((DifferentialGradedBimodule.Derived.fromBimodules A B).map f).op =
      (derivedBifunctorObjIso T').hom ≫ derivedNatTrans f ≫
        (derivedBifunctorObjIso T).inv := sorry

variable (T : (DifferentialGradedBimodule.Derived.Category.{u, v, w, x} A B)ᵒᵖ)

#synth (derivedBifunctor A B).Additive
#synth Functor.Linear R (derivedBifunctor A B)
#synth ((derivedBifunctor A B).obj T).Additive
#synth Functor.Linear R ((derivedBifunctor A B).obj T)
#synth ((derivedBifunctor A B).obj T).CommShift ℤ
#synth ((derivedBifunctor A B).obj T).IsTriangulated

end DifferentialGradedBimodule.InternalHom
