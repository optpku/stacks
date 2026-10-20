module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Pushforward.PseudoCoherentDual
import StacksCheckRecall

/-!
# Dual of a relatively perfect internal Hom after derived pushforward

Along a proper, flat, finitely presented morphism of algebraic spaces with
quasi-compact quasi-separated target, the derived pushforward of the internal
Hom from a pseudo-coherent complex to a relatively perfect complex is the
internal Hom of a pseudo-coherent complex into the structure sheaf, and the
same complex remains valid after every cartesian base change.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

/- Lemma 76.52.11: the pushforward of derived sheaf Hom from a pseudo-coherent
complex to a relatively perfect complex is a pseudo-coherent dual, compatibly
with arbitrary cartesian base change using the same complex on the target. -/
@[stacks 0DKY] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.exists_pseudoCoherent_dual :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [IsQuasiCompact Y] → [IsAbsolutelyQuasiSeparated Y] →
      [Proper f] → [Flat f] → [FinitePresentation f] →
      ∀ (E K : ModuleDerived X), ModuleDerived.IsPerfectRelativeTo f E →
        IsPseudoCoherent X K →
        ∃ L : ModuleDerived Y,
          IsPseudoCoherent Y L ∧
            IsIsomorphic
              ((Modules.moduleDerivedPushforward f).obj (ModuleDerived.InternalHom.obj K E))
              (ModuleDerived.InternalHom.obj L (structureSheafDerived Y)) ∧
            ∀ {X' Y' : AlgebraicSpace S}
              (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y),
              IsPullback g' f' f g →
                IsIsomorphic
                  ((Modules.moduleDerivedPushforward f').obj
                    (ModuleDerived.InternalHom.obj
                      ((ModuleDerived.pullback g').obj K) ((ModuleDerived.pullback g').obj E)))
                  (ModuleDerived.InternalHom.obj
                    ((ModuleDerived.pullback g).obj L) (structureSheafDerived Y')))
