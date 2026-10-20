module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.VectorBundle
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace

/-!
# Vector-bundle loci of derived pushforwards

For a proper, flat, finitely presented morphism and a finitely presented module flat
over the target, being a vector bundle of fixed integer rank in one degree after
base change is represented by an open subspace of the target.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The derived pushforward of the ordinary pullback of a module to the fiber product,
placed in degree zero, along the projection to the test space. -/
abbrev baseChangeDerivedPushforward {T : AlgebraicSpace S} (f : X ⟶ Y) (g : T ⟶ Y)
    (F : X.Modules) : ModuleDerived T :=
  (Modules.moduleDerivedPushforward (Limits.pullback.snd f g)).obj
    ((DerivedCategory.singleFunctor (Modules (Limits.pullback f g)) 0).obj
      ((Modules.pullback (Limits.pullback.fst f g)).obj F))

/-- The base-changed derived pushforward is the derived pushforward along the second
projection of the degree-zero placement of the pullback along the first projection. -/
theorem baseChangeDerivedPushforward_eq {T : AlgebraicSpace S} (f : X ⟶ Y) (g : T ⟶ Y)
    (F : X.Modules) :
    baseChangeDerivedPushforward f g F =
      (Modules.moduleDerivedPushforward (Limits.pullback.snd f g)).obj
        ((DerivedCategory.singleFunctor (Modules (Limits.pullback f g)) 0).obj
          ((Modules.pullback (Limits.pullback.fst f g)).obj F)) :=
  rfl

/-- For a proper, flat, finitely presented morphism and a finitely presented module flat
over the target, there exists an open subspace through which a morphism factors exactly
when the base-changed derived pushforward is a finite locally free module of the given
integer rank placed in the given integer degree. -/
theorem exists_pushforwardVectorBundleLocus
    (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f]
    (F : X.Modules) (hF_fp : F.IsFinitePresentation) (hF_flat : Modules.flatOver F f)
    (i r : ℤ) :
    ∃ V : OpenSubspace Y, ∀ {T : AlgebraicSpace S} (g : T ⟶ Y),
      (∃ lift : T ⟶ V.X, lift ≫ V.ι = g) ↔
        IsVectorBundleOfRankInDegree (baseChangeDerivedPushforward f g F) i r :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
