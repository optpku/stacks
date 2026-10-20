module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic

/-!
# Locally finite type étale slice

The locally finite type étale slice of a scheme, its constant coefficient sheaf, and the
restriction and locality operations for sheaves of modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Schemes locally of finite type over `S`, regarded as objects over `S`. -/
abbrev locallyOfFiniteTypeOver (S : Scheme.{u}) :=
  MorphismProperty.Over (@LocallyOfFiniteType) ⊤ S

/-- The structure morphism of a locally finite type object is locally of finite type. -/
instance instLocallyOfFiniteType_hom {S : Scheme.{u}} (V : locallyOfFiniteTypeOver S) :
    LocallyOfFiniteType V.hom :=
  V.prop

/-- The étale topology restricted to schemes locally of finite type over `S`. -/
def etaleTopology (S : Scheme.{u}) :
    GrothendieckTopology (locallyOfFiniteTypeOver S) :=
  (MorphismProperty.Over.forget (@LocallyOfFiniteType) ⊤ S).restrictedTopology
    (S.overGrothendieckTopology @Etale)

/-- The constant sheaf of rings with value `Λ` on the locally finite type étale slice. -/
def constantRingSheaf (S : Scheme.{u}) (Λ : Type u) [Ring Λ]
    [HasWeakSheafify (etaleTopology S) RingCat.{u}] :
    Sheaf (etaleTopology S) RingCat.{u} :=
  (constantSheaf (etaleTopology S) RingCat.{u}).obj (RingCat.of Λ)

/-- Sheaves of modules over the constant ring sheaf on the locally finite type étale slice. -/
abbrev modules (S : Scheme.{u}) (Λ : Type u) [Ring Λ]
    [HasWeakSheafify (etaleTopology S) RingCat.{u}] :=
  SheafOfModules.{u} (constantRingSheaf S Λ)

/-- Sheaf restriction along a morphism in the locally finite type étale slice. -/
theorem restriction {S : Scheme.{u}} {Λ : Type u} [Ring Λ]
    [HasWeakSheafify (etaleTopology S) RingCat.{u}]
    {U V : locallyOfFiniteTypeOver S} (f : U ⟶ V)
    (ℱ : SheafOfModules.{u} ((constantRingSheaf S Λ).over V)) :
    (⊤ : ObjectProperty (SheafOfModules.{u} ((constantRingSheaf S Λ).over U)))
      ((SheafOfModules.overMap (constantRingSheaf S Λ) f).obj ℱ) :=
  sorry

/-- Membership in the module category is local for coverings in the restricted étale topology. -/
theorem local_iff {S : Scheme.{u}} {Λ : Type u} [Ring Λ]
    [HasWeakSheafify (etaleTopology S) RingCat.{u}]
    {U : locallyOfFiniteTypeOver S}
    {cover : FormalCoproduct.{u} (Over U)}
    (hcover : ((etaleTopology S).over U).CoversTop cover.obj)
    (ℱ : SheafOfModules.{u} ((constantRingSheaf S Λ).over U)) :
    (⊤ : ObjectProperty (SheafOfModules.{u} ((constantRingSheaf S Λ).over U))) ℱ ↔
      ∀ i : cover.I,
        (⊤ : ObjectProperty
            (SheafOfModules.{u} ((constantRingSheaf S Λ).over (cover.obj i).left)))
          ((SheafOfModules.overMap (constantRingSheaf S Λ) (cover.obj i).hom).obj ℱ) :=
  sorry

end AlgebraicGeometry.Scheme.Etale
