module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RelativeDualizing
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 48.12.7 (1): the relative dualizing complex of a proper flat morphism of finite
presentation over a quasi-compact quasi-separated scheme is perfect relative to the base. -/
@[stacks 0E4L] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.relativeDualizingComplex_isPerfectRelativeTo :
    ∀ {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
      (f : X ⟶ Y) [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
      (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh X)
      (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a),
      Scheme.ModuleDerived.IsPerfectRelativeTo f
        (Scheme.DerivedQCoh.relativeDualizingComplex f a aAdjunction).obj)

/- Lemma 48.12.7 (2): the derived pushforward of the relative dualizing complex has
zero cohomology sheaves in every positive degree. -/
@[stacks 0E4L] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.relativeDualizingPushforward_cohomology_isZero_of_pos :
    ∀ {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
      (f : X ⟶ Y) [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
      (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh X)
      (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a)
      (i : ℤ), 0 < i →
      IsZero (RingedSpace.ModuleDerived.cohomologySheaf
        ((Scheme.DerivedQCoh.pushforwardCohomologyIn f).obj
          (Scheme.DerivedQCoh.relativeDualizingComplex f a aAdjunction)).obj i))

/- Lemma 48.12.7 (3): the canonical homothety from the tensor unit to the derived
endomorphism object of the relative dualizing complex is invertible. -/
@[stacks 0E4L] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.relativeDualizingHomothetyIsIso :
    ∀ {X Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
      (f : X ⟶ Y) [IsProper f] [Flat f] [Scheme.Hom.FinitePresentation f]
      [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
      (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh X)
      (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a)
      (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)),
      let ω := (Scheme.DerivedQCoh.relativeDualizingComplex f a aAdjunction).obj
      IsIso (@MonoidalClosed.curry'
        (RingedSpace.ModuleDerived X.toRingedSpace) _ _ ω ω (H.closed ω) (𝟙 ω)))
