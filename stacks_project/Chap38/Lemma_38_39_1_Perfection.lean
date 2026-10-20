/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Colimit.VectorBundle

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.FrobeniusColimit

#check (ringSheafMap : ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p],
  S.ringCatSheaf ⟶ S.ringCatSheaf)

#check (ringSheafMap_app : ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
  (U : S.Opens) (s : S.presheaf.obj (.op U)),
  RingCat.Hom.hom ((ringSheafMap p S).hom.app (.op U)) s = s ^ p)

#check (ringSheafDiagram : ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p],
  ℕ ⥤ TopCat.Sheaf RingCat.{u} S)

#check (ringSheafDiagram_obj : ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
  (n : ℕ), (ringSheafDiagram p S).obj n = S.ringCatSheaf)

#check (ringSheafDiagram_map_succ : ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
  [S.IsCharP p] (n : ℕ),
  (ringSheafDiagram p S).map (homOfLE n.le_succ) = ringSheafMap p S)

#check (ringSheaf : ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p],
  TopCat.Sheaf RingCat.{u} S)

#check (toRingSheaf : ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
  (n : ℕ), S.ringCatSheaf ⟶ ringSheaf p S)

#check (toRingSheaf_succ : ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
  (n : ℕ), ringSheafMap p S ≫ toRingSheaf p S (n + 1) = toRingSheaf p S n)

#check (toRingSheaf_naturality : ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
  [S.IsCharP p] {i j : ℕ} (f : i ⟶ j),
  (ringSheafDiagram p S).map f ≫ toRingSheaf p S j =
    toRingSheaf p S i ≫ ((Functor.const ℕ).obj (ringSheaf p S)).map f)

#check (ringSheafCocone : ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p],
  Cocone (ringSheafDiagram p S))

#check (ringSheafDesc : ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
  (c : Cocone (ringSheafDiagram p S)), ringSheaf p S ⟶ c.pt)

#check (ringSheafDesc_fac : ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
  (c : Cocone (ringSheafDiagram p S)) (n : ℕ),
  toRingSheaf p S n ≫ ringSheafDesc p S c = c.ι.app n)

#check (ringSheafDesc_uniq : ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
  (c : Cocone (ringSheafDiagram p S)) (f : ringSheaf p S ⟶ c.pt)
  (_ : ∀ n, toRingSheaf p S n ≫ f = c.ι.app n), f = ringSheafDesc p S c)

#check (ringSheafCoconeIsColimit : ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
  [S.IsCharP p], IsColimit (ringSheafCocone p S))

#check (vectorBundles : Scheme.{u} → Cat.{u + 1, u + 1})

#check (vectorBundles_property : ∀ (S : Scheme.{u}) (E : vectorBundles S),
  Scheme.Modules.IsFiniteLocallyFree (ULift.down E).obj)

#check (pullback_mapsTo : ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p],
  (fun E : S.Modules ↦ Scheme.Modules.IsFiniteLocallyFree E) ≤
    ObjectProperty.inverseImage
      (fun E : S.Modules ↦ Scheme.Modules.IsFiniteLocallyFree E)
      (Scheme.Modules.pullback (Scheme.absoluteFrobenius p S)))

#check (pullback : ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p],
  vectorBundles S ⥤ vectorBundles S)

#check (pullback_obj : ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
  (E : vectorBundles S),
  (ULift.down ((pullback p S).obj E)).obj =
    (Scheme.Modules.pullback (Scheme.absoluteFrobenius p S)).obj (ULift.down E).obj)

#check (vectorBundleDiagram : ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p],
  ℕ ⥤ Cat.{u + 1, u + 1})

#check (vectorBundleDiagram_obj : ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
  [S.IsCharP p] (n : ℕ), (vectorBundleDiagram p S).obj n = vectorBundles S)

#check (vectorBundleDiagram_map_succ : ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
  [S.IsCharP p] (n : ℕ),
  (vectorBundleDiagram p S).map (homOfLE n.le_succ) = (pullback p S).toCatHom)

#check (vectorBundleColimit : ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p],
  Cat.{u + 1, u + 1})

#check (stage : ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p] (n : ℕ),
  vectorBundles S ⥤ vectorBundleColimit p S)

#check (stage_succ : ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
  (n : ℕ), pullback p S ⋙ stage p S (n + 1) = stage p S n)

#check (finiteLocallyFreeModules : ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
  [S.IsCharP p], Cat.{u + 1, u + 1})

#check (finiteLocallyFreeModules_property : ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
  [S.IsCharP p] (E : finiteLocallyFreeModules p S),
  (fun M : SheafOfModules.{u} (ringSheaf p S) ↦
    SheafOfModules.IsFiniteLocallyFree M) (ULift.down E).obj)

#check (vectorBundlesEquiv : ∀ (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [S.IsCharP p]
  [CompactSpace S] [QuasiSeparatedSpace S],
  Nonempty (vectorBundleColimit p S ≌ finiteLocallyFreeModules p S))

end AlgebraicGeometry.Scheme.FrobeniusColimit
