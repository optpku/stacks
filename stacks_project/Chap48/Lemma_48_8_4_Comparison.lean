module

public import stacks_project.Chap48.«48_8_0_1_Comparison»
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint.Composition

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat
open CategoryTheory.MonoidalCategory
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Compatibility checks for the promoted derived-quasicoherent composition API. -/
#check (pullbackCompAppIso : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  (hPullback : IsIso (RingedSpace.modulePullbackDerived.compComparison
    f.toShHom g.toShHom)) (K : DerivedQCoh Z),
  (pullback f).obj ((pullback g).obj K) ≅ (pullback (f ≫ g)).obj K)

#check (pullbackCompAppIso_naturality : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  (hPullback : IsIso (RingedSpace.modulePullbackDerived.compComparison
    f.toShHom g.toShHom)) {K L : DerivedQCoh Z} (k : K ⟶ L),
  (pullback f).map ((pullback g).map k) ≫ (pullbackCompAppIso f g hPullback L).hom =
    (pullbackCompAppIso f g hPullback K).hom ≫ (pullback (f ≫ g)).map k)

#check (pullbackCompIso : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  (hPullback : IsIso (RingedSpace.modulePullbackDerived.compComparison
    f.toShHom g.toShHom)), pullback g ⋙ pullback f ≅ pullback (f ≫ g))

#check (pushforwardCompIso : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
  [QuasiCompact (f ≫ g)] [QuasiSeparated (f ≫ g)]
  (hPullback : IsIso (RingedSpace.modulePullbackDerived.compComparison
    f.toShHom g.toShHom)), pushforward f ⋙ pushforward g ≅ pushforward (f ≫ g))

#check (compositeRightAdjunction : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
  [QuasiCompact (f ≫ g)] [QuasiSeparated (f ≫ g)]
  (hPullback : IsIso (RingedSpace.modulePullbackDerived.compComparison
    f.toShHom g.toShHom)) (a : DerivedQCoh Y ⥤ DerivedQCoh X)
  (b : DerivedQCoh Z ⥤ DerivedQCoh Y) (aAdjunction : pushforward f ⊣ a)
  (bAdjunction : pushforward g ⊣ b), pushforward (f ≫ g) ⊣ b ⋙ a)

#check (pullbackTensorIso : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HomotopyTensorDescends X.toRingedSpace] [TensorDescends X.toRingedSpace]
  [IsLocalization X.toRingedSpace]
  [HomotopyTensorDescends Y.toRingedSpace] [TensorDescends Y.toRingedSpace]
  [IsLocalization Y.toRingedSpace]
  [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
  (K L : DerivedQCoh Y),
  (pullback f).obj (tensorObj K L) ≅ tensorObj ((pullback f).obj K) ((pullback f).obj L))

#check (pullbackTensorCompIso : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [HomotopyTensorDescends X.toRingedSpace] [TensorDescends X.toRingedSpace]
  [IsLocalization X.toRingedSpace]
  [HomotopyTensorDescends Y.toRingedSpace] [TensorDescends Y.toRingedSpace]
  [IsLocalization Y.toRingedSpace]
  [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
  (hPullback : IsIso (RingedSpace.modulePullbackDerived.compComparison
    f.toShHom g.toShHom)) (K : DerivedQCoh Z) (L : DerivedQCoh Y) (E : DerivedQCoh X),
  tensorObj ((pullback f).obj (tensorObj ((pullback g).obj K) L)) E ≅
    tensorObj (tensorObj ((pullback (f ≫ g)).obj K) ((pullback f).obj L)) E)

#check (tensorObjAssocMapRight : ∀ {X : Scheme.{u}}
  [HomotopyTensorDescends X.toRingedSpace] [TensorDescends X.toRingedSpace]
  [IsLocalization X.toRingedSpace]
  (A B C D : DerivedQCoh X) (m : tensorObj B C ⟶ D),
  tensorObj (tensorObj A B) C ⟶ tensorObj A D)

end AlgebraicGeometry.Scheme.DerivedQCoh
