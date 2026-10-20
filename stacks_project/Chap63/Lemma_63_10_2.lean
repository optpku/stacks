/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.HomologyBounds
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Bounds
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open DerivedCategory DerivedCategory.TStructure

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Y : Scheme.{u}} (X : Over Y) {Λ : Type u} [CommRing Λ]
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [hXqc : CompactSpace X.left] [hXqs : QuasiSeparatedSpace X.left]

variable [HasSheafify (smallEtaleTopology X.left) (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify ((smallEtaleTopology X.left).over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))]
variable [HasSheafify (smallEtaleTopology Y) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify ((smallEtaleTopology Y).over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))]

variable [GrothendieckTopology.HasSheafCompose (smallEtaleTopology X.left)
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

/- Lemma 63.10.2: derived lower shriek has one uniform bound for both truncation
comparisons and for homology supported in intervals with finite or infinite
endpoints, independently of the chosen compactification realization. -/
@[stacks 0G2A] #check
  (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.exists_isGE_isLE X :
    ∃ N : ℤ, ∀ (P : Compactification.Of Y X)
      [HasSheafify (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)]
      [∀ U : (Over.left P.obj.right).Etale,
        HasWeakSheafify ((smallEtaleTopology (Over.left P.obj.right)).over U)
          (ModuleCat.{u} Λ)]
      [HasDerivedCategory
        (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))]
      [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
        (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
      [(etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} Λ)).Additive]
      [PreservesFiniteLimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
      [PreservesFiniteColimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
      [((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) (smallEtaleTopology Y)
          (smallEtaleTopology (Over.left P.obj.right))).Additive]
      [HasRightDerivedFunctor
        (RightDerived.Cochain.toDerived
          ((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous
            (ModuleCat.{u} Λ) (smallEtaleTopology Y)
            (smallEtaleTopology (Over.left P.obj.right))))
        (HomologicalComplex.quasiIso
          (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))
          (ComplexShape.up ℤ))]
      (E : DerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)))
      (_hE : AddMonoid.IsTorsion Λ ∨
        (etaleDerivedIsTorsion E ∧ ∃ n, IsGE E n)),
      (∀ (a i : ℤ), i ≤ a →
        IsIso
          ((homologyFunctor
              (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)) i).map
            ((etaleDerivedLowerShriek X P).map ((t.truncLEι a).app E)))) ∧
      (∀ (b i : ℤ), b ≤ i →
        IsIso
          ((homologyFunctor
              (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)) i).map
            ((etaleDerivedLowerShriek X P).map ((t.truncGEπ (b - N)).app E)))) ∧
      (∀ (a b : EInt), a ≤ b →
        (∀ i : ℤ, ¬ (a ≤ (i : EInt) ∧ (i : EInt) ≤ b) →
          IsZero ((homologyFunctor
            (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)) i).obj E)) →
        ∀ i : ℤ, ¬ (a ≤ (i : EInt) ∧ ((i - N : ℤ) : EInt) ≤ b) →
          IsZero ((homologyFunctor
            (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ)) i).obj
              ((etaleDerivedLowerShriek X P).obj E))))

end AlgebraicGeometry.Scheme.Etale
