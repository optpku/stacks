module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.ClosedImmersion
import StacksCheckRecall

/-!
# Lemma 67.14.1

For a closed immersion of algebraic spaces, the adjunction unit induces
`F / I F ≅ i_* i^* F`, the counit `i^* i_* G ⟶ G` is an isomorphism, and
quasi-coherent pushforward is exact and fully faithful with essential image
the modules annihilated by the kernel ideal sheaf of `i`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 67.14.1: for a closed immersion, the adjunction unit identifies every
module modulo the defining ideal action with its pullback followed by pushforward. -/
@[stacks 04CJ] #check
  (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.isIso_quotientByIdealComparison :
    ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
      (F : X.Modules), IsIso (Modules.quotientByIdealComparison i F))

#check (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.isIso_modulesAdjunction_counit :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i],
    IsIso (Modules.pullbackPushforwardAdjunction i).counit)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.pushforward_exact :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i],
    exactFunctor Z.Modules X.Modules (Modules.pushforward i))

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.pushforwardExact :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i],
    exactFunctor (QCoh Z) (QCoh X) (QCoh.pushforward i))

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.pushforward.full :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i],
    (QCoh.pushforward i).Full)

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.pushforward.faithful :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i],
    (QCoh.pushforward i).Faithful)

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.mem_essImage_iff_isAnnihilatedByKernel :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    (H : QCoh X),
    (QCoh.pushforward i).essImage H ↔
      SheafOfModules.IsAnnihilatedByKernel
        (SheafOfModules.ChangeOfRings.homOverId (structureSheafMap i)) H.obj)

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.mem_essImage_iff_idealSheaf_smul_eq_zero :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    (H : QCoh X),
    (QCoh.pushforward i).essImage H ↔
      ∀ U : (smallEtaleSite X)ᵒᵖ,
        ∀ s : (Hom.idealSheaf i).val.obj U,
          ∀ m : H.obj.val.obj U,
            ((Hom.idealSheafι i).val.app U s) • m = 0)
