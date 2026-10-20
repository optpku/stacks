module

public import ReasLib.CategoryTheory.GaloisFunctorDiagram
import StacksCheckRecall

@[expose] public section

open CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory

universe uC vC uC' vC' uC'' vC'' w

namespace CategoryTheory.GaloisFunctorDiagram

/- Lemma 58.4.5: in the Galois-category diagram, the image of `h'` is normal
if and only if every connected object mapping from the terminal object is a
finite coproduct of terminal objects. -/
@[stacks 0BTS]
#check (@CategoryTheory.GaloisFunctorDiagram.normalRange_iff_finiteCoproductTerminal :
  (C : Type uC) → [Category.{vC} C] → [GaloisCategory C] →
    (C' : Type uC') → [Category.{vC'} C'] → [GaloisCategory C'] →
    (C'' : Type uC'') → [Category.{vC''} C''] → [GaloisCategory C''] →
    (F : C ⥤ FintypeCat.{w}) → [FiberFunctor F] →
    (F' : C' ⥤ FintypeCat.{w}) → [FiberFunctor F'] →
    (F'' : C'' ⥤ FintypeCat.{w}) → [FiberFunctor F''] →
    (D : GaloisFunctorDiagram F F' F'') →
      Subgroup.Normal (MonoidHom.range D.h'.toMonoidHom) ↔
        ∀ (X' : C') [PreGaloisCategory.IsConnected X'],
          Nonempty ((⊤_ C'') ⟶ D.H'.obj X') →
            ∃ n : ℕ, ∃ Y : Fin n → C'',
              (∀ i, Nonempty (IsTerminal (Y i))) ∧
                Nonempty ((∐ Y) ≅ D.H'.obj X'))

end CategoryTheory.GaloisFunctorDiagram
