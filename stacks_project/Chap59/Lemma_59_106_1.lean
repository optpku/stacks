/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.TopologyComparison.MayerVietoris
import StacksCheckRecall

@[expose] public section

universe u v

open CategoryTheory
open CategoryTheory.GrothendieckTopology.Derived.Sections.MayerVietoris
open CategoryTheory.GrothendieckTopology.Derived.Absolute

/- Lemma 59.106.1 (0EWN): with the notation of the almost blowup square, an object in the
essential image of the topology-comparison right-derived direct image satisfies the canonical
Mayer--Vietoris condition, hence the comparison maps c^K_{X,Z,X',E} are quasi-isomorphisms. -/
@[stacks 0EWN] #check
  (@CategoryTheory.GrothendieckTopology.Derived.Absolute.MayerVietoris.condition_of_essImage :
    ∀ {C : Type u} [Category.{v, u} C] {τ τ' : GrothendieckTopology C}
      [HasSheafify τ AddCommGrpCat.{max u v}]
      [HasSheafify τ' AddCommGrpCat.{max u v}]
      [IsGrothendieckAbelian.{max u v} (SiteAbelianSheafCat τ')]
      [HasWeakSheafify τ (Type (max u v))] (hle : τ' ≤ τ)
      [Functor.HasRightDerivedFunctor
        (Functor.Homotopy.toDerived
          (CategoryTheory.GrothendieckTopology.Derived.Absolute.pushforward hle))
        (CategoryTheory.GrothendieckTopology.Derived.Absolute.qis τ)]
      (S : Square C),
      IsPushout
        (τ.sheafifiedRepresentableMap S.toY)
        (τ.sheafifiedRepresentableMap S.toZ)
        (τ.sheafifiedRepresentableMap S.inY)
        (τ.sheafifiedRepresentableMap S.inZ) →
      Mono (τ.sheafifiedRepresentableMap S.toY) →
      ∀ (K' : DerivedCategory (SiteAbelianSheafCat τ')),
        Functor.essImage
          (CategoryTheory.GrothendieckTopology.Derived.Absolute.rightDerived hle) K' →
        S.Condition τ' K')

end
