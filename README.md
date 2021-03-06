В файле Check в папке src лежит реализация Чёрч-style типизации лямбда термов и соответствующий тайп-чекер. Стратегия написания кода понятна и относительно проста:

1) создаем пользовательские типы данных Expr и Type для лямбда-выражений и типов соответственно. При этом не забывая, что в термах при абстракции мы должны указать, как именно типизуется переменная, по которой мы абстрагируем. В качестве реализации контекста мною выбран тип данных Map, в котором ключи будут использоваться для обозначения термовых переменных, а значения ключей, естественно, будут показывать, каким типом в контексте у нас типизуется ключ;

2) далее пишем функцию выведения типов, которая по контексту и терму выдает Maybe Type. В случае успешной типизации мы получаем, собственно, тип, в котором типизовался данных на вход терм. Если терм не типизуем в данном контексте мы получим Nothing;

3) реализуем сам check, он прост: сравнивает тип, который мы подали на вход, с тем типом, который выдала функция выведения типов. В итоге получаем значение типа Bool.

Инструкция по запуску:

Чтобы запустить функцию выведения типов, вызовите в компиляторе: env "Контекст" "Терм". Здесь контекст упакован в Map, поэтому для удобства напишите список ключей со значениями в виде [(k1,type1),(k2,type2),...] и вызовите на этом списке fromList. Как написать нужный терм, понятно из кода, где написана реализация типа данных Expr. Тут стоит отметить, что так как у нас типизация по Чёрчу, то в контекст формально нельзя вводить одинаковые ключи, помните об этом. Вы, конечно, так сделать можете, но fromList автоматически реализует в Map только последнее введение ключа.

Чтобы запустить функцию проверки, вызовите в компиляторе: check "Список ключей со значениями" "Терм" "Тип". Тут для удоства не нужно список ключей со значениями сразу переводить в Map, за вас сделает это сам check.

Также я написал 15 тестов, которые нормально компилирует cabal локально, но, к сожалению, я так и не смог поднять CI :( Так-как что гит, что CI я поднимал впервые в жизни и то с помощью относительно шаряшего друга :D Тем не менее, оставлю код с тестами тут, смотрите файл с именем testlambda.


P.S. Реализованная функция типизации термов будет типизовать некоторые термы, которые формально не типизуются по Чёрчу, например: \x^{\alpha}.\x^{beta}.x. Однако при типизации написанный агоритм будет воспринимать два одинаковых икса как бы как разные, и поэтому наш терм оттипизуется вполне ожидаемым типом: \alpha -> \beta -> \beta. Можно было, конечно, некоторыми естественными образами бороться с этим, но я оставил всё как есть для того, чтобы написанный eval и check были аналогичны по действию подобным функциям в Coq.
