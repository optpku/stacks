module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject.Regularity
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 31.20.6 (1): a regular sheaf of ideals on a scheme is of finite type. -/
@[stacks 063F]
#check (AlgebraicGeometry.Scheme.IdealSubobject.isFiniteType_of_isRegular :
  ∀ {X : AlgebraicGeometry.Scheme.{u}} (I : AlgebraicGeometry.Scheme.IdealSubobject X),
    [AlgebraicGeometry.RingedSpace.IsRegularIdealSheaf I] → I.toModule.IsFiniteType)

/- Lemma 31.20.6 (2): a regular sheaf of ideals on a scheme is quasi-coherent. -/
@[stacks 063F]
#check (AlgebraicGeometry.Scheme.IdealSubobject.isQuasicoherent_of_isRegular :
  ∀ {X : AlgebraicGeometry.Scheme.{u}} (I : AlgebraicGeometry.Scheme.IdealSubobject X),
    [AlgebraicGeometry.RingedSpace.IsRegularIdealSheaf I] → I.toModule.IsQuasicoherent)

/- Lemma 31.20.6 (3): a Koszul-regular sheaf of ideals on a scheme is of finite type. -/
@[stacks 063F]
#check (AlgebraicGeometry.Scheme.IdealSubobject.isFiniteType_of_isKoszulRegular :
  ∀ {X : AlgebraicGeometry.Scheme.{u}} (I : AlgebraicGeometry.Scheme.IdealSubobject X),
    [AlgebraicGeometry.RingedSpace.IsKoszulRegularIdealSheaf I] → I.toModule.IsFiniteType)

/- Lemma 31.20.6 (4): a Koszul-regular sheaf of ideals on a scheme is quasi-coherent. -/
@[stacks 063F]
#check (AlgebraicGeometry.Scheme.IdealSubobject.isQuasicoherent_of_isKoszulRegular :
  ∀ {X : AlgebraicGeometry.Scheme.{u}} (I : AlgebraicGeometry.Scheme.IdealSubobject X),
    [AlgebraicGeometry.RingedSpace.IsKoszulRegularIdealSheaf I] → I.toModule.IsQuasicoherent)

/- Lemma 31.20.6 (5): an H₁-regular sheaf of ideals on a scheme is of finite type. -/
@[stacks 063F]
#check (AlgebraicGeometry.Scheme.IdealSubobject.isFiniteType_of_isH1Regular :
  ∀ {X : AlgebraicGeometry.Scheme.{u}} (I : AlgebraicGeometry.Scheme.IdealSubobject X),
    [AlgebraicGeometry.RingedSpace.IsH1RegularIdealSheaf I] → I.toModule.IsFiniteType)

/- Lemma 31.20.6 (6): an H₁-regular sheaf of ideals on a scheme is quasi-coherent. -/
@[stacks 063F]
#check (AlgebraicGeometry.Scheme.IdealSubobject.isQuasicoherent_of_isH1Regular :
  ∀ {X : AlgebraicGeometry.Scheme.{u}} (I : AlgebraicGeometry.Scheme.IdealSubobject X),
    [AlgebraicGeometry.RingedSpace.IsH1RegularIdealSheaf I] → I.toModule.IsQuasicoherent)

/- Lemma 31.20.6 (7): a quasi-regular sheaf of ideals on a scheme is of finite type. -/
@[stacks 063F]
#check (AlgebraicGeometry.Scheme.IdealSubobject.isFiniteType_of_isQuasiRegular :
  ∀ {X : AlgebraicGeometry.Scheme.{u}} (I : AlgebraicGeometry.Scheme.IdealSubobject X),
    [AlgebraicGeometry.RingedSpace.IsQuasiRegularIdealSheaf I] → I.toModule.IsFiniteType)

/- Lemma 31.20.6 (8): a quasi-regular sheaf of ideals on a scheme is quasi-coherent. -/
@[stacks 063F]
#check (AlgebraicGeometry.Scheme.IdealSubobject.isQuasicoherent_of_isQuasiRegular :
  ∀ {X : AlgebraicGeometry.Scheme.{u}} (I : AlgebraicGeometry.Scheme.IdealSubobject X),
    [AlgebraicGeometry.RingedSpace.IsQuasiRegularIdealSheaf I] → I.toModule.IsQuasicoherent)
