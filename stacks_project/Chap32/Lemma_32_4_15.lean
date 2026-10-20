module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Limit.Ample
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry

universe u

/- Lemma 32.4.15: in Situation 32.4.5, let `ℒ₀` be an invertible sheaf of modules on the
distinguished stage `S₀`. If its pullback to the limit scheme `S` is ample, then after passing to
some stage `Sᵢ` over `S₀`, the pullback `ℒᵢ` is ample. -/
@[stacks 09MT] #check
  (AlgebraicGeometry.Scheme.Modules.exists_stage_isAmple_pullback_of_isAmple_limit_pullback :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
      (i₀ : I) (ℒ₀ : (D.obj i₀).Modules) [Scheme.Modules.Invertible ℒ₀]
      [Scheme.Modules.IsAmple ((Scheme.Modules.pullback (c.π.app i₀)).obj ℒ₀)],
      ∃ (i : I) (hi : i₀ ≤ i),
        Scheme.Modules.IsAmple
          ((Scheme.Modules.pullback (D.map (homOfLE hi))).obj ℒ₀))
