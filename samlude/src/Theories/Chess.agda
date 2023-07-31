{-# OPTIONS --cubical --cumulativity #-}
module Theories.Chess where

open import Foundations.Prelude
open import Foundations.Equiv
open import Foundations.Decidable

open import Control.Eq

open Eq {{...}}

open import Categories.Category
open import Categories.Functor
open import Categories.NaturalTransformation
open import Categories.CATS
open import Categories.TYPE
open import Categories.Diagram.Two
open import Categories.Diagram.Zero

open Functor {{...}}
open IsCategory {{...}}
open Terminal {{...}} renaming (D to 𝓓)

open import Data.Fin
open import Data.Bool


{-
RankFile : Rank ≃ File
fst RankFile 0 = A
fst RankFile 1 = B
fst RankFile 2 = C
fst RankFile 3 = D
fst RankFile 4 = E
fst RankFile 5 = F
fst RankFile 6 = G
fst RankFile 7 = H
equiv-proof (snd RankFile) A = ({!0!} , {!!}) , {!!}
equiv-proof (snd RankFile) B = {!!}
equiv-proof (snd RankFile) C = {!!}
equiv-proof (snd RankFile) D = {!!}
equiv-proof (snd RankFile) E = {!!}
equiv-proof (snd RankFile) F = {!!}
equiv-proof (snd RankFile) G = {!!}
equiv-proof (snd RankFile) H = {!!}
-}

data Player : Type where
  B W : Player

opp : Player → Player
opp B = W
opp W = B

data Piece : Type where
  P Q K B N R : Piece

data File : Type where
  A B C D E F G H : File

Rank : Type
Rank = Fin 7


data SquareData : Type where
  occupied : Player → Piece → SquareData
  unoccupied : SquareData

record Position : Type where
  field
    ToMove   : Player
    Castling : Player × Bool → Bool
    Pieces   : Rank × File → SquareData

data GameState : Type where
  GameOver : (Player ＋ ⊤) → GameState
  Ongoing : Position → GameState

drawn : GameState
drawn = GameOver (unsym inj₁ (! 0))

won : Player → GameState
won = GameOver ∘ (unsym {_} {ℓ-suc ℓ-zero} inj₀)

data RelativeRank : Type where
  QR KR QB KB QN KN Q K : RelativeRank

fromRel : Player → RelativeRank → File → (Rank × File)
fromRel = {!!}

-- Partial position is a
PositionF : ∀ {ℓ} → Functor (TYPE ℓ) (TYPE ℓ)
Functor.F0 PositionF X = Rank × File → X
Functor.F1 PositionF f pos x = f (pos x)


PosP : ∀ {ℓ} → Type (ℓ-suc ℓ)
PosP {ℓ} = PositionF .F0 (SquareData → Type ℓ)
module PosPs where
  ∙ : PosP
  ∙ _ _ = ⊤

  instance
    rfeq : Eq (Rank × File)
    (rfeq Eq.≟ a) b = {!!}

  [_:=_] : (Rank × File) → SquareData → PosP
  [ homePos := x ] pos d with homePos ≟ pos
  ... | yes _ = x ≡ d
  ... | no  _ = ⊤

data HalfTurn (x : Player) : Position → Position → Type where
  1stPawn : ∀ {x} → {!!}

data Turn : GameState → GameState → Type where
  Resign : ∀ {x : Player} {p : Position} → Turn (Ongoing p) (won (opp x))
  Draw   : ∀ {p : Position} → Turn (Ongoing p) drawn
  Move   : ∀ {x : Player} {g h} → HalfTurn x g h → Turn (Ongoing g) (Ongoing h)


open import Categories.Category.Free

CHESS : Category ℓ-zero ℓ-zero
CHESS = Free GameState Turn
