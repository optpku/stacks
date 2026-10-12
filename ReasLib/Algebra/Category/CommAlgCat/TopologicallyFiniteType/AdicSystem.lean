/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommAlgCat.AdicQuotient
public import ReasLib.Algebra.Category.CommAlgCat.TopologicallyFiniteType

/-!
# Adic systems of topologically finite type algebras

An adically complete algebra with finite-type special fiber determines a
finite-type adic inverse system by taking its positive adic quotients.
-/

@[expose] public section

open CategoryTheory

universe u

namespace CommAlgCat.TopologicallyFiniteType

variable {A : Type u} [CommRing A]

/-- The quotient-system morphism induced by an identity algebra map is the identity. -/
theorem toAdicSystem_map_id (I : Ideal A) (B : TopologicallyFiniteType.{u} A I) :
    AdicAlgebraSystem.ofHom (adicQuotientUnderMap I (𝟙 B : B ⟶ B).hom.hom) =
      𝟙 (AdicAlgebraSystem.of A I (adicQuotientUnder I B.obj)) := sorry

/-- The quotient-system morphisms induced by algebra maps preserve composition. -/
theorem toAdicSystem_map_comp (I : Ideal A) {B C D : TopologicallyFiniteType.{u} A I}
    (f : B ⟶ C) (g : C ⟶ D) :
    AdicAlgebraSystem.ofHom (adicQuotientUnderMap I (f ≫ g).hom.hom) =
      AdicAlgebraSystem.ofHom (adicQuotientUnderMap I f.hom.hom) ≫
        AdicAlgebraSystem.ofHom (adicQuotientUnderMap I g.hom.hom) := sorry

/-- The functor sending a topologically finite type algebra to its adic quotient system. -/
noncomputable def toAdicSystem (I : Ideal A) :
    TopologicallyFiniteType.{u} A I ⥤ AdicAlgebraSystem A I where
  obj B := AdicAlgebraSystem.of A I (adicQuotientUnder I B.obj)
  map f := AdicAlgebraSystem.ofHom (adicQuotientUnderMap I f.hom.hom)
  map_id := toAdicSystem_map_id I
  map_comp := toAdicSystem_map_comp I

/-- The stage at `n` of the image of `B` is the quotient by the extension of `I ^ n`. -/
theorem toAdicSystem_obj_stage (I : Ideal A) (B : TopologicallyFiniteType.{u} A I) (n : ℕ+) :
    ((toAdicSystem I).obj B).obj.right.stage n =
      CommRingCat.of (B.obj ⧸ (I ^ (n : ℕ)).map (algebraMap A B.obj)) := sorry

/-- The component at `n` of the image of an algebra map is the induced map on adic quotients. -/
theorem toAdicSystem_map_app (I : Ideal A) {B C : TopologicallyFiniteType.{u} A I}
    (f : B ⟶ C) (n : ℕ+) :
    (Under.Hom.right ((toAdicSystem I).map f).hom).app (OrderDual.toDual n) =
      CommRingCat.ofHom (adicQuotientMap I f.hom.hom n) := sorry

/-- Each stage structure map of the image adic system is of finite type. -/
theorem toAdicSystem_finiteType_stage (I : Ideal A) (B : TopologicallyFiniteType.{u} A I)
    (n : ℕ+) :
    (AdicAlgebraSystem.stageAlgebraMap I ((toAdicSystem I).obj B).obj n).FiniteType := sorry

end CommAlgCat.TopologicallyFiniteType
