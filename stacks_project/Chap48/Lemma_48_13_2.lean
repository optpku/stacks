module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.OpenRestriction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 48.13.2: a right adjoint to derived quasicoherent pushforward along a perfect proper
morphism of Noetherian schemes preserves closed support under inverse image. -/
@[stacks 0AAA] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.rightAdjoint_isSupportedOn_preimage_of_perfect_proper :
    ∀ {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
      (f : X ⟶ Y) [IsProper f] [LocallyOfType RingHom.IsPerfectRingMap f]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X)
      (aAdjunction : pushforwardCohomologyIn f ⊣ a)
      (T : TopologicalSpace.Closeds Y) (Q : DerivedQCoh Y)
      (hQ : RingedSpace.ModuleDerived.IsSupportedOn Q.obj (T : Set Y)),
      RingedSpace.ModuleDerived.IsSupportedOn
        (a.obj Q).obj (T.preimage f.continuous : Set X))

/- The open-restriction clause uses the canonical right-adjoint mate associated to the
cartesian restriction square. -/
#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.rightAdjoint_openRestrictionComparison_isIso_of_perfect_proper :
    ∀ {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
      (f : X ⟶ Y) [IsProper f] [LocallyOfType RingHom.IsPerfectRingMap f]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X)
      (aAdjunction : pushforwardCohomologyIn f ⊣ a)
      (V : Y.Opens)
      (aV : DerivedQCoh V.toScheme ⥤ DerivedQCoh (f ⁻¹ᵁ V).toScheme)
      (aVAdjunction : pushforwardCohomologyIn (f ∣_ V) ⊣ aV)
      (K : DerivedQCoh Y),
      IsIso
        ((DerivedBaseChange.mapOfRight
          (pullbackPushforwardAdjunction V.ι)
          (pullbackPushforwardAdjunction (f ⁻¹ᵁ V).ι)
          (@asIso _ _ _ _
            (BaseChange.rightMate
              (f ⁻¹ᵁ V).ι (f ∣_ V) f V.ι
              (isPullback_morphismRestrict f V).flip.toCommSq
              a aV aAdjunction aVAdjunction)
            (BaseChange.rightMate_isIso_of_perfect_proper_open_restriction
              f a aAdjunction V aV aVAdjunction)).inv).app K))

end AlgebraicGeometry.Scheme.DerivedQCoh
