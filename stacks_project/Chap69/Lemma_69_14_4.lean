module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Devissage
import StacksCheckRecall

/-!
# Lemma 69.14.4

On a Noetherian algebraic space, an extension-closed property of coherent modules
which contains the zero sheaf and holds for pushforwards of quasi-coherent ideal
sheaves from reduced closed subspaces with irreducible underlying space holds for
every coherent sheaf.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open scoped ZeroObject

noncomputable section

universe u

/- Lemma 69.14.4: let `S` be a scheme, let `X` be a Noetherian algebraic space over
`S`, and let `P` be a property of coherent `𝒪_X`-modules. Assume `P` holds for the
zero sheaf. Assume that for any short exact sequence `0 ⟶ F₁ ⟶ F ⟶ F₂ ⟶ 0` of
coherent sheaves, if `F₁` and `F₂` have property `P` then so does `F`. Assume that
for every reduced closed subspace `i : Z ⟶ X` with `|Z|` irreducible and every
quasi-coherent sheaf of ideals `I ⊂ 𝒪_Z`, property `P` holds for
`(pushforward i).obj I.toModule`. Then `P` holds for every coherent sheaf on `X`. -/
@[stacks 07US] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.coherent_property_of_shortExact_and_pushforward_ideal :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (P : X.Modules → Prop)
    (h_zero : P (0 : X.Modules))
    (h_shortExact :
      ∀ {C : ShortComplex X.Modules}, C.ShortExact →
        C.X₁.IsCoherent → C.X₂.IsCoherent → C.X₃.IsCoherent →
        P C.X₁ → P C.X₃ → P C.X₂)
    (h_pushforward_ideal :
      ∀ (Z : AlgebraicSpace S) (i : Z ⟶ X),
        IsClosedImmersion i → IsReduced Z → IsIrreducible Z →
          ∀ (I : IdealSubobject Z), IsQuasiCoherent I →
            P ((pushforward i).obj I.toModule))
    (F : X.Modules) [F.IsCoherent],
    P F)
