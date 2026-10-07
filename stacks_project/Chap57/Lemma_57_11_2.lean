module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.MatlisDuality
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry.SchemeOverField

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

open DerivedCategory.DerivedTensor RingedSpace RingedSpace.ModuleDerived

/- Lemma 57.11.2: on a regular scheme of finite type over a field, a coherent module supported
at a closed point represents, on perfect derived modules, degree-zero derived global sections
after tensoring with a shifted coherent module whose stalk is its Matlis dual. -/
@[stacks 0G02]
#check
  (AlgebraicGeometry.Scheme.homIsoTensorMatlisDualAt :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k),
      [Hom.FiniteType X.hom] → [Regular X.left] →
      (x : X.left) → x ∈ closedPoints X.left →
      (F F' : CohSupportedOn X.left.toRingedSpace {x}) →
      (E : Type u) → [AddCommGroup E] → [Module (stalkRing X x) E] →
      [Module.Injective (stalkRing X x) E] →
      (ι : IsLocalRing.ResidueField (stalkRing X x) →ₗ[stalkRing X x] E) →
      ι.IsInjectiveHull →
      (stalkModuleCat F'.obj.obj x ≅
        ModuleCat.of (stalkRing X x) (stalkModuleCat F.obj.obj x →ₗ[stalkRing X x] E)) →
      (d : ℕ) → ringKrullDim (stalkRing X x) = (d : WithBot ℕ∞) →
      Nonempty
        ((Perfect.ι ⋙
            preadditiveCoyoneda.obj
              (op ((DerivedCategory.singleFunctor X.left.Modules 0).obj F.obj.obj))) ≅
          (Perfect.ι ⋙
            Right.functor
              (((DerivedCategory.singleFunctor X.left.Modules 0).obj F'.obj.obj)⟦-(d : ℤ)⟧) ⋙
            moduleDerivedCohomologyFunctor X.left.toRingedSpace 0 ⋙
            forget₂ (ModuleCat (globalSectionsRing X.left.toRingedSpace)) AddCommGrpCat.{u} ⋙
            AddCommGrpCat.uliftFunctor.{u + 1, u})))

end AlgebraicGeometry.Scheme
