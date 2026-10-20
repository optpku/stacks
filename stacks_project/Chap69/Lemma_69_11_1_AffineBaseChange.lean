module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.AffineBaseChange

/-!
# Affine pushforward, vanishing, and cartesian base change

Along an affine morphism of algebraic spaces, pushforward of a quasi-coherent module remains
quasi-coherent, higher direct images vanish in positive degree, and underived pushforward
commutes with arbitrary cartesian base change.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

universe u

#check
  (Modules.pushforward.isRightAdjoint :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      (Modules.pushforward f).IsRightAdjoint)

section

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f]
variable (F : X.Modules) [F.IsQuasicoherent]

#check
  (Modules.pushforward.isQuasicoherent f F :
    ((Modules.pushforward f).obj F).IsQuasicoherent)

#check
  (Modules.pushforward.isQuasicoherentOf f (inferInstance : F.IsQuasicoherent) :
    ((Modules.pushforward f).obj F).IsQuasicoherent)

end

section

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

#check
  (Modules.higherDirectImage_isZero_of_affine :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f]
      [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
      (F : X.Modules) [F.IsQuasicoherent] (i : ℕ),
      0 < i → IsZero (Modules.higherDirectImage f F i))

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f]
variable [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]

#check
  ((Modules.pushforward f).rightDerivedZeroIsoSelf :
    (Modules.pushforward f).rightDerived 0 ≅ Modules.pushforward f)

end

#check
  (Modules.affineBaseChange_pushforward_isomorphic :
    ∀ {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
      (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y),
      IsPullback g' f' f g → ∀ [Affine f] (F : X.Modules) [F.IsQuasicoherent],
        IsIsomorphic ((Modules.pullback g).obj ((Modules.pushforward f).obj F))
          ((Modules.pushforward f').obj ((Modules.pullback g').obj F)))
