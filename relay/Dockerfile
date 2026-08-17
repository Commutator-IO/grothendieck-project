# No dependencies, so no install step and no lockfile: the relay is one file
# that uses only Node's standard library. Measured at 228 MB, essentially all
# of it the Node runtime — the relay's own contribution is a few kilobytes.
FROM node:22-alpine
WORKDIR /app
# allowed.json too, and not only server.mjs: it is the list of community
# documents the relay may fetch, generated from editions.json. Left out of the
# image, every /edition/<slug>.pdf answers "No such edition document" — which is
# what happened, because the file was added after this line was written.
COPY server.mjs allowed.json ./
ENV PORT=8080
EXPOSE 8080
# Run as the image's unprivileged user: the relay needs no filesystem access
# at all, and nothing it does should be able to touch the container.
USER node
CMD ["node", "server.mjs"]
