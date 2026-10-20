module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Restriction.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.MayerVietoris

/-! # Gluing derived modules along an elementary distinguished square -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {U V X : AlgebraicSpace S}
variable (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]

/-- The canonical isomorphism between the two successive restrictions of a global
derived module object to the overlap `U ×_X V`. -/
def restrictFunctorDerivedOverlapIso (F : ModuleDerived X) :
    (restrictFunctorDerived (Limits.pullback.fst j f)).obj
        ((restrictFunctorDerived j).obj F) ≅
      (restrictFunctorDerived (Limits.pullback.snd j f)).obj
        ((restrictFunctorDerived f).obj F) :=
  (restrictFunctorDerivedCompIso j (Limits.pullback.fst j f)).app F ≪≫
    (restrictFunctorDerived_eqToIso (fiberHom_eq j f)).app F ≪≫
    (restrictFunctorDerivedCompIso f (Limits.pullback.snd j f)).symm.app F

/-- Restriction of a morphism `A ⟶ E|_U` to `W = U ×_X V`, as a morphism
`A|_W ⟶ E|_W`. -/
def moduleDerivedGlueRestrictU {A : ModuleDerived U} {E : ModuleDerived X}
    (a : A ⟶ (restrictFunctorDerived j).obj E) :
    (restrictFunctorDerived (Limits.pullback.fst j f)).obj A ⟶
      (restrictFunctorDerived (fiberHom j f)).obj E :=
  (restrictFunctorDerived (Limits.pullback.fst j f)).map a ≫
    (restrictFunctorDerivedCompIso j (Limits.pullback.fst j f)).hom.app E

/-- Restriction of a morphism `B ⟶ E|_V` to `W = U ×_X V`, as a morphism
`B|_W ⟶ E|_W`. -/
def moduleDerivedGlueRestrictV {B : ModuleDerived V} {E : ModuleDerived X}
    (b : B ⟶ (restrictFunctorDerived f).obj E) :
    (restrictFunctorDerived (Limits.pullback.snd j f)).obj B ⟶
      (restrictFunctorDerived (fiberHom j f)).obj E :=
  (restrictFunctorDerived (Limits.pullback.snd j f)).map b ≫
    (restrictFunctorDerivedCompIso f (Limits.pullback.snd j f)).hom.app E ≫
    (restrictFunctorDerived_eqToIso (fiberHom_eq j f).symm).hom.app E

/-- Compatibility of a pair of morphisms `A ⟶ E|_U` and `B ⟶ E|_V` with an overlap
isomorphism `c` on `W = U ×_X V`. -/
def moduleDerivedGlueHomCompatible (A : ModuleDerived U) (B : ModuleDerived V)
    (c : (restrictFunctorDerived (Limits.pullback.fst j f)).obj A ≅
      (restrictFunctorDerived (Limits.pullback.snd j f)).obj B)
    (E : ModuleDerived X) (a : A ⟶ (restrictFunctorDerived j).obj E)
    (b : B ⟶ (restrictFunctorDerived f).obj E) : Prop :=
  moduleDerivedGlueRestrictU j f a = c.hom ≫ moduleDerivedGlueRestrictV j f b

/-- Derived module objects on an elementary distinguished square with an overlap
isomorphism admit a global object and compatible restriction isomorphisms. Every
compatible pair of morphisms into restrictions of a global object extends to a
morphism from this glued object with the prescribed restrictions. -/
theorem exists_moduleDerivedGlue [IsElementaryDistinguishedSquare j f]
    (A : ModuleDerived U) (B : ModuleDerived V)
    (c : (restrictFunctorDerived (Limits.pullback.fst j f)).obj A ≅
      (restrictFunctorDerived (Limits.pullback.snd j f)).obj B) :
    ∃ (F : ModuleDerived X)
      (eU : (restrictFunctorDerived j).obj F ≅ A)
      (eV : (restrictFunctorDerived f).obj F ≅ B),
      (c.hom =
        (restrictFunctorDerived (Limits.pullback.fst j f)).map eU.inv ≫
          (restrictFunctorDerivedOverlapIso j f F).hom ≫
          (restrictFunctorDerived (Limits.pullback.snd j f)).map eV.hom) ∧
      ∀ (E : ModuleDerived X) (a : A ⟶ (restrictFunctorDerived j).obj E)
        (b : B ⟶ (restrictFunctorDerived f).obj E),
        moduleDerivedGlueHomCompatible j f A B c E a b →
        ∃ φ : F ⟶ E,
          (restrictFunctorDerived j).map φ = eU.hom ≫ a ∧
            (restrictFunctorDerived f).map φ = eV.hom ≫ b :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
