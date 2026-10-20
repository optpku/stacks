module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalDeformation.Functoriality

/-!
# Change-of-ring maps on infinitesimal and tangent modules

The canonical change-of-ring maps are available from their mathematical owner.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open AlgebraicGeometry.GroupoidsOver

universe u

#check (AlgebraicGeometry.GroupoidsOver.infMap :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y),
(infFunctor x).obj M ⟶
      (ModuleCat.restrictScalars v.hom).obj ((infFunctor y).obj N))

#check (AlgebraicGeometry.GroupoidsOver.tangentMap :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y),
(tangentFunctor x).obj M ⟶
      (ModuleCat.restrictScalars.{u + 1} v.hom).obj ((tangentFunctor y).obj N))
