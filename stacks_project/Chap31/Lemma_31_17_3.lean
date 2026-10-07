module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Norm.Morphism
import StacksCheckRecall

/-!
# Lemma 31.17.3

Norms of morphisms between invertible modules.

@stack 0BCZ
-/

@[expose] public section

universe u

/- Lemma 31.17.3: A norm for a finite morphism sends each morphism of invertible modules to a
morphism between the corresponding normed representatives, and the induced residue-fiber map
vanishes exactly over the image of the original morphism's residue-fiber zero locus. -/
@[stacks 0BCZ] #check
  (AlgebraicGeometry.Scheme.exists_picardNormMap_zeroAt_iff :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (π : X ⟶ Y) (d : ℕ)
      [AlgebraicGeometry.IsFinite π],
      (∃ N : AlgebraicGeometry.Scheme.FiniteMorphismNorm π,
        AlgebraicGeometry.Scheme.IsFiniteMorphismNorm π d N) →
      ∃ normπ : X.PicardGroup →+ Y.PicardGroup,
        (∀ (𝒩 : Y.Modules)
          [CategoryTheory.MonoidalCategory.isInvertibleObject 𝒩],
          normπ (AlgebraicGeometry.Scheme.Hom.picardPullbackClass π 𝒩) =
            d • AlgebraicGeometry.Scheme.Modules.picardClass 𝒩) ∧
          ∀ (ℒ ℒ' : X.Modules)
            [CategoryTheory.MonoidalCategory.isInvertibleObject ℒ]
            [CategoryTheory.MonoidalCategory.isInvertibleObject ℒ'] (φ : ℒ ⟶ ℒ'),
            ∃ normφ :
              AlgebraicGeometry.Scheme.PicardGroup.repr
                  (normπ (AlgebraicGeometry.Scheme.Modules.picardClass ℒ)) ⟶
                AlgebraicGeometry.Scheme.PicardGroup.repr
                  (normπ (AlgebraicGeometry.Scheme.Modules.picardClass ℒ')),
              ∀ y : Y,
                ((∃ x : {x : X // π.base x = y},
                    AlgebraicGeometry.Scheme.Modules.fiberMap φ x.1 = 0) ↔
                  AlgebraicGeometry.Scheme.Modules.fiberMap normφ y = 0))
