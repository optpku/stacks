/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_11_1_Formal

/-!
# Étale covering by formal algebraic spaces

A sheaf on `(Sch/S)_fppf` that admits a jointly sheaf-surjective family of
maps from formal algebraic spaces, each representable by algebraic spaces and
étale, is itself a formal algebraic space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry
namespace IsFormalAlgebraicSpace

/-- Lemma 87.15.1: Let `S` be a scheme. Let `{π i : X_ i ⟶ X}_{i : ι}` be a
family of maps of sheaves on `(Sch/S)_fppf`. Assume (a) each `X_ i` is a
formal algebraic space over `S`, (b) each `π i` is representable by algebraic
spaces and étale, and (c) the coproduct desc `Cofan.IsColimit.desc hc π` is a
surjection of sheaves. Then `X` is a formal algebraic space over `S`. -/
@[stacks 0AJ1]
theorem ofEtaleCover {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {ι : Type (max u v)} {X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c)
    (hX : ∀ i, IsFormalAlgebraicSpace (X_ i)) (hπ : ∀ i, etale (π i))
    (h_surj : Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π)) :
    IsFormalAlgebraicSpace X := sorry

end IsFormalAlgebraicSpace
end AlgebraicGeometry
