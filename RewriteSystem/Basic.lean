variable {α : Type _} [DecidableEq α]

abbrev RewriteRule (α : Type _) := List α × List α

abbrev RewriteSystem (α : Type _) := List (RewriteRule α)

def List.rewriteHead? : (pre post w : List α) → Option (List α)
  | [], post, w => some (post ++ w)
  | a :: pre', post, b :: w' =>
    if a = b then
      rewriteHead? pre' post w' 
    else
      none
  | _, _, [] => none

def List.rewriteAtAux? (r : RewriteRule α) (pre : List α) : (pos : Nat) → (w : List α) → Option (List α)
  | .zero, w => pre.reverseAux <$> rewriteHead? r.fst r.snd w
  | .succ m, a :: w' => rewriteAtAux? r (a :: pre) m w'
  | .succ _, [] =>  none

def List.rewriteAt? (r : RewriteRule α) := List.rewriteAtAux? r []

#eval [0, 1, 2, 3, 4].rewriteAt? ⟨[2], [10, 15]⟩ 2

inductive Derivation (R : RewriteSystem α) : List α → List α → Prop
  | refl : (w : List α) → Derivation R w w
  | trans {w w' w'' : List α} : (r : RewriteRule α) → r ∈ R → 
      (pos : Nat) → List.rewriteAt? r pos w = some w' →
        Derivation R w' w'' → Derivation R w w'' 

