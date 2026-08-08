# No dependencies, so no install step and no lockfile: the relay is one file
# that uses only Node's standard library. Alpine keeps the image at ~60 MB.
FROM node:22-alpine
WORKDIR /app
COPY server.mjs .
ENV PORT=8080
EXPOSE 8080
# Run as the image's unprivileged user: the relay needs no filesystem access
# at all, and nothing it does should be able to touch the container.
USER node
CMD ["node", "server.mjs"]
