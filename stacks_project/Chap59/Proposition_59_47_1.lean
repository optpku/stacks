module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.IntegralEmbedding
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Small-étale pushforward of sheaves of sets along a morphism of schemes. -/
noncomputable abbrev smallEtalePushforwardType {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf X.smallEtaleTopology (Type u) ⥤ Sheaf Y.smallEtaleTopology (Type u) :=
  Scheme.smallEtaleDirectImage.{u,u} f

end AlgebraicGeometry.Scheme.Etale

/- Proposition 59.47.1 (1): small-étale direct image of sets is full. -/
@[stacks 04FZ] #check
  (AlgebraicGeometry.Scheme.Etale.smallEtalePushforward_integralUnivInj_type_full :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f],
      (Scheme.smallEtaleDirectImage.{u,u} f).Full)

/- Proposition 59.47.1 (2): small-étale direct image of sets is faithful. -/
@[stacks 04FZ] #check
  (AlgebraicGeometry.Scheme.Etale.smallEtalePushforward_integralUnivInj_type_faithful :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f],
      (Scheme.smallEtaleDirectImage.{u,u} f).Faithful)

/- Proposition 59.47.1 (3): the set-valued essential image is terminal off the image. -/
@[stacks 04FZ] #check
  (AlgebraicGeometry.Scheme.Etale.mem_essImage_smallEtalePushforward_type_iff :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f]
      (F : Sheaf Y.smallEtaleTopology (Type u)),
      (Scheme.smallEtaleDirectImage.{u,u} f).essImage F ↔
        AlgebraicGeometry.Scheme.Etale.restrictsToTerminalOnImageComplement f F)

/- Proposition 59.47.1 (4): set-valued inverse image is a left inverse to direct image. -/
@[stacks 04FZ] #check
  (AlgebraicGeometry.Scheme.Etale.isIso_counit_smallEtalePushforward_integralUnivInj_type :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f],
      IsIso ((Scheme.smallEtalePullback f).sheafAdjunctionContinuous
        (Type u) Y.smallEtaleTopology X.smallEtaleTopology).counit)

/- Proposition 59.47.1 (5): small-étale direct image of abelian sheaves is full. -/
@[stacks 04FZ] #check
  (AlgebraicGeometry.Scheme.Etale.smallEtalePushforward_integralUnivInj_ab_full :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f],
      (AlgebraicGeometry.Scheme.Etale.smallEtalePushforwardAb f).Full)

/- Proposition 59.47.1 (6): small-étale direct image of abelian sheaves is faithful. -/
@[stacks 04FZ] #check
  (AlgebraicGeometry.Scheme.Etale.smallEtalePushforward_integralUnivInj_ab_faithful :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f],
      (AlgebraicGeometry.Scheme.Etale.smallEtalePushforwardAb f).Faithful)

/- Proposition 59.47.1 (7): the abelian essential image consists of sheaves supported
inside the image. -/
@[stacks 04FZ] #check
  (AlgebraicGeometry.Scheme.Etale.mem_essImage_smallEtalePushforward_ab_iff :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f]
      (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}),
      (AlgebraicGeometry.Scheme.Etale.smallEtalePushforwardAb f).essImage F ↔
        AlgebraicGeometry.Scheme.Etale.abelianSheafSupport F ⊆ Set.range f.base)

/- Proposition 59.47.1 (8): abelian inverse image is a left inverse to direct image. -/
@[stacks 04FZ] #check
  (AlgebraicGeometry.Scheme.Etale.isIso_counit_smallEtalePushforward_integralUnivInj_ab :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f],
      IsIso ((Scheme.smallEtalePullback f).sheafAdjunctionContinuous
        AddCommGrpCat.{u} Y.smallEtaleTopology X.smallEtaleTopology).counit)
