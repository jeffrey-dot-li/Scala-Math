// object Runeterra
// {
//     object CardType extends Enumeration 
//     {
//         type CardType = Value;
//         val Spell, Unit, Landmark = Value;   
//     }

//     abstract class Card(val id: Int)
//     {
        
//     };
//     class Spell extends Card
//     {

//     }
    
//     class Unit extends Card
//     {
//         object Keyword extends Enumeration 
//         {
//             type Keyword = Value;
//             val QuickAttack, Overwhelm, SpellShield = Value;
//         }
//     }


//     type CardList = Array[Card];
//     // Array is mutable and indexed.
//     class Deck(val cards : CardList)
//     {
//         var CurrentDeck = cards;
//         def Draw() = { 
//             val last = CurrentDeck.last; 
//             CurrentDeck.dropRight(1);
//             last;
//         }
        
//     };


//     class Players (val first: Player, val second : Player)
//     {

//         implicit def FromTuple(tuple : Tuple2[Player, Player]) : Players = new Players(tuple._1, tuple._2);
        
//         def asTuple = (first, second)
//         def Inverted = new Players(second, first);
//     }




//     class Game(val players: Players)
//     {
//         var round = 0;
//         type PlayerRun = Player => Any;
//         def PlayersTurnOrder = if (round % 2 == 0) players.Inverted else players;

//         def PlayersBoth(fn: PlayerRun) =
//         {
//             val (first, second) = PlayersTurnOrder.asTuple;
//             fn.apply(first);
//             fn.apply(second);
//         }

//         def StartRound() = 
//         {
//             round +=1;

//             PlayersBoth(v => v.RoundStart());
//             PlayersBoth(v => v.Draw());
//         }
//         def Start()
//         {

//         }
//     }

//     class Player(val deck : Deck)
//     {
//         var Hand : CardList = {};

//         def RoundStart() = {};
//         def Draw() = {
//             Hand :+ deck.Draw();
//         };
//     }
// }