//> using options -opt -opt-inline:** -Ybackend-parallelism:8

// Backend workers load ClassBTypes from classfiles concurrently (here MethodHandles$Lookup, found in
// invokedynamic bootstrap handles). A worker must not see a ClassBType another one is still initializing.
trait Client[F[_]]
type Middleware[F[_]] = Client[F] => Client[F]

trait ClientMiddleware[F[_]] extends Middleware[F] {
  def wrapClient(client: Client[F]): Client[F]
  final def apply(client: Client[F]): Client[F] = wrapClient(client)
  final def wrapMiddleware(that: Middleware[F]): ClientMiddleware[F] =
    (client: Client[F]) => wrapClient(that(client))
}

trait IO[T]
def middleware: ClientMiddleware[IO] = (client: Client[IO]) => client

def test =
  middleware
  .wrapMiddleware(middleware)
  .wrapClient(new Client[IO] {})
