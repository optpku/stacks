module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

/-!
# Coextension of scalars along an ideal quotient

Coextension from a commutative ring to its quotient by an ideal is naturally isomorphic to the
functor of elements annihilated by that ideal.
-/

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.ModuleCat.IdealTorsion

variable {A : Type u} [CommRing A]

/-- A linear map carries the submodule annihilated by an ideal into the corresponding
submodule of its codomain. -/
theorem map_mem (I : Ideal A) {M N : ModuleCat.{max u v} A} (f : M ⟶ N)
    (x : Submodule.torsionBySet A M I) : f x ∈ Submodule.torsionBySet A N I := sorry

/-- The map on ideal-annihilated submodules induced by a linear map. -/
def map (I : Ideal A) {M N : ModuleCat.{max u v} A} (f : M ⟶ N) :
    ModuleCat.of (A ⧸ I) (Submodule.torsionBySet A M I) ⟶
      ModuleCat.of (A ⧸ I) (Submodule.torsionBySet A N I) :=
  ModuleCat.ofHom <|
    LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective <|
      (f.hom.comp (Submodule.subtype (Submodule.torsionBySet A M I))).codRestrict
        (Submodule.torsionBySet A N I) (map_mem I f)

/-- The induced map acts by the original linear map on underlying elements. -/
theorem map_apply (I : Ideal A) {M N : ModuleCat.{max u v} A} (f : M ⟶ N)
    (x : Submodule.torsionBySet A M I) : (map I f x : N) = f x := sorry

/-- The ideal-torsion map induced by an identity morphism is the identity. -/
theorem map_id (I : Ideal A) (M : ModuleCat.{max u v} A) :
    map I (𝟙 M) = 𝟙 (ModuleCat.of (A ⧸ I) (Submodule.torsionBySet A M I)) := sorry

/-- Taking ideal-torsion submodules respects composition. -/
theorem map_comp (I : Ideal A) {M N P : ModuleCat.{max u v} A} (f : M ⟶ N) (g : N ⟶ P) :
    map I (f ≫ g) = map I f ≫ map I g := sorry

/-- The functor sending an `A`-module `M` to the `A ⧸ I`-module of elements annihilated
by every element of `I`. -/
def functor (I : Ideal A) : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} (A ⧸ I) where
  obj M := ModuleCat.of (A ⧸ I) (Submodule.torsionBySet A M I)
  map f := map I f
  map_id := map_id I
  map_comp := map_comp I

/-- The object part of `functor` is the submodule annihilated by every element of `I`. -/
theorem obj (I : Ideal A) (M : ModuleCat.{max u v} A) :
    (functor I).obj M = ModuleCat.of (A ⧸ I) (Submodule.torsionBySet A M I) := sorry

/-- The map part of `functor` is induced by restricting the original linear map. -/
theorem map_eq (I : Ideal A) {M N : ModuleCat.{max u v} A} (f : M ⟶ N) :
    (functor I).map f = map I f := sorry

/-- Evaluation at `1 : A ⧸ I` of a map `A ⧸ I →ₗ[A] M` is annihilated by `I`. -/
theorem eval_mem (I : Ideal A) (M : ModuleCat.{max u v} A)
    (g : (ModuleCat.coextendScalars (Ideal.Quotient.mk I)).obj M) :
    ((ModuleCat.RestrictionCoextensionAdj.counit' (Ideal.Quotient.mk I)).app M) g ∈
      Submodule.torsionBySet A M I := sorry

/-- Evaluation at `1 : A ⧸ I` as an `A ⧸ I`-linear morphism from coextension to the
ideal-annihilated submodule. -/
def eval (I : Ideal A) (M : ModuleCat.{max u v} A) :
    (ModuleCat.coextendScalars (Ideal.Quotient.mk I)).obj M ⟶ (functor I).obj M :=
  ModuleCat.ofHom
    { toFun := fun g ↦ ⟨((ModuleCat.RestrictionCoextensionAdj.counit'
        (Ideal.Quotient.mk I)).app M) g, eval_mem I M g⟩
      map_add' := sorry
      map_smul' := sorry }

/-- Evaluation at the quotient-ring unit is the underlying formula for `eval`. -/
theorem eval_apply (I : Ideal A) (M : ModuleCat.{max u v} A)
    (g : (ModuleCat.coextendScalars (Ideal.Quotient.mk I)).obj M) :
    (eval I M g).1 =
      ModuleCat.CoextendScalars.equiv (Ideal.Quotient.mk I) M g (1 : A ⧸ I) := sorry

/-- An ideal-annihilated element determines the linear map from `A ⧸ I` obtained by
scalar multiplication followed by inclusion into the ambient module. -/
def lift (I : Ideal A) (M : ModuleCat.{max u v} A) :
    (functor I).obj M ⟶ (ModuleCat.coextendScalars (Ideal.Quotient.mk I)).obj M :=
  ModuleCat.ofHom
    { toFun := fun x ↦ (ModuleCat.CoextendScalars.equiv (Ideal.Quotient.mk I) M).symm
        { toFun := fun (q : A ⧸ I) ↦ ((q • x : Submodule.torsionBySet A M I) : M)
          map_add' := sorry
          map_smul' := sorry }
      map_add' := sorry
      map_smul' := sorry }

/-- Under the concrete coextension equivalence, `lift` sends `x` to the map `q ↦ q • x`. -/
theorem lift_apply (I : Ideal A) (M : ModuleCat.{max u v} A)
    (x : Submodule.torsionBySet A M I) (q : A ⧸ I) :
    ModuleCat.CoextendScalars.equiv (Ideal.Quotient.mk I) M (lift I M x) q =
      ((q • x : Submodule.torsionBySet A M I) : M) := sorry

/-- Evaluation followed by the canonical lift is the identity on coextension. -/
theorem eval_lift (I : Ideal A) (M : ModuleCat.{max u v} A) :
    eval I M ≫ lift I M = 𝟙 ((ModuleCat.coextendScalars (Ideal.Quotient.mk I)).obj M) := sorry

/-- The canonical lift followed by evaluation is the identity on the ideal-annihilated
submodule. -/
theorem lift_eval (I : Ideal A) (M : ModuleCat.{max u v} A) :
    lift I M ≫ eval I M = 𝟙 ((functor I).obj M) := sorry

/-- Coextension along `A ⟶ A ⧸ I` is objectwise isomorphic to the submodule annihilated
by `I`. -/
noncomputable def iso (I : Ideal A) (M : ModuleCat.{max u v} A) :
    (ModuleCat.coextendScalars (Ideal.Quotient.mk I)).obj M ≅ (functor I).obj M :=
  CategoryTheory.Iso.mk (eval I M) (lift I M) (eval_lift I M) (lift_eval I M)

/-- Evaluation at `1` commutes with every morphism of `A`-modules. -/
theorem eval_naturality (I : Ideal A) {M N : ModuleCat.{max u v} A} (f : M ⟶ N) :
    (ModuleCat.coextendScalars (Ideal.Quotient.mk I)).map f ≫ eval I N =
      eval I M ≫ (functor I).map f := sorry

/-- Coextension along `A ⟶ A ⧸ I` is naturally isomorphic to the ideal-torsion functor. -/
noncomputable def natIso (I : Ideal A) :
    ModuleCat.coextendScalars (Ideal.Quotient.mk I) ≅ functor I :=
  NatIso.ofComponents (fun M ↦ iso I M) (eval_naturality I)

/-- A component of `natIso` is the canonical objectwise isomorphism. -/
theorem natIso_app (I : Ideal A) (M : ModuleCat.{max u v} A) :
    (natIso I).app M = iso I M := sorry

/-- The forward component of `natIso` is evaluation at `1`. -/
theorem natIso_hom_app (I : Ideal A) (M : ModuleCat.{max u v} A) :
    (natIso I).hom.app M = eval I M := sorry

/-- The inverse component of `natIso` is the canonical lift from the ideal-annihilated
submodule. -/
theorem natIso_inv_app (I : Ideal A) (M : ModuleCat.{max u v} A) :
    (natIso I).inv.app M = lift I M := sorry

end CategoryTheory.ModuleCat.IdealTorsion
