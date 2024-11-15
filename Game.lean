-- import Game.Levels.DemoWorld
import Game.Levels.Derivative
import Game.Levels.Limit

-- Here's what we'll put on the title screen
Title "Calculus Game"
Introduction
"

This text appears on the starting page where one selects the world/level to play.
You can use markdown.
"

Info "
## Calculus Game

This game is intended for a fun introduction to Lean4 and Calculus World.
"

/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "An experimental game for Calculus in Lean4"
CaptionLong "This game is intended for a fun introduction to Lean4 and Calculus World."
-- Prerequisites "" -- add this if your game depends on other games
CoverImage "images/cover_test.jpg"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
